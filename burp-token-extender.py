# -*- coding: utf-8 -*-
#
# Burp Suite Extension (Jython) - Per-user JWT bearer refresh on 401/403
#
# Requirements:
# - Burp Suite with Jython configured (Jython 2.7)
#
# What it does:
# - Injects latest cached Bearer token per user into outgoing requests.
# - Refreshes tokens per user using a refresh-token mapping when:
#   (A) a response comes back with configured failure codes (default 401,403), OR
#   (B) pre-emptively when the current JWT is near expiry.
#
# Performance notes:
# - JWT payload decoding is done ONCE per distinct token string and cached (token -> {username, exp}).
# - Requests using the same token do O(1) lookups + time check (no repeated decoding).
#
# Important change vs previous version:
# - Pre-emptive refresh is SYNCHRONOUS (only when exp <= now+skew), so the same request can succeed.
#   This avoids "still expired" responses due to async timing.
#
from burp import IBurpExtender, ITab, IHttpListener

from java.awt import BorderLayout, GridBagLayout, GridBagConstraints, Insets
from javax.swing import JPanel, JLabel, JTextField, JTextArea, JScrollPane, JButton, JCheckBox

from java.util import Base64
from java.lang import Runnable, Thread
from java.util.concurrent.locks import ReentrantLock
from java.net import URL
from java.lang import System

import json


class _Runnable(Runnable):
    """Jython-friendly Runnable wrapper."""
    def __init__(self, fn):
        self._fn = fn

    def run(self):
        self._fn()


class BurpExtender(IBurpExtender, ITab, IHttpListener):

    def registerExtenderCallbacks(self, callbacks):
        self._callbacks = callbacks
        self._helpers = callbacks.getHelpers()
        callbacks.setExtensionName("JWT Bearer Auto-Refresh (Per User)")

        self._lock = ReentrantLock()
        self._token_by_username = {}      # username -> latest access_token
        self._refreshing_user = set()     # usernames currently refreshing (for async path)

        # token_string -> {"username": str|None, "exp": int|None}
        self._token_meta = {}
        self._token_meta_max = 2000

        # UI
        self._main = JPanel(BorderLayout())
        self._panel = JPanel(GridBagLayout())
        self._main.add(self._panel, BorderLayout.NORTH)

        c = GridBagConstraints()
        c.insets = Insets(4, 4, 4, 4)
        c.fill = GridBagConstraints.HORIZONTAL
        c.weightx = 1.0

        row = 0

        self._refresh_url = JTextField("http://127.0.0.1:8000/auth/refresh")
        self._add_row(c, row, "Refresh URL:", self._refresh_url); row += 1

        self._refresh_method = JTextField("POST")
        self._add_row(c, row, "Refresh Method:", self._refresh_method); row += 1

        self._body_template = JTextField('{"refresh_token":"{refresh_token}"}')
        self._add_row(c, row, "Refresh Body Template:", self._body_template); row += 1

        self._content_type = JTextField("application/json")
        self._add_row(c, row, "Refresh Content-Type:", self._content_type); row += 1

        self._access_field = JTextField("access_token")
        self._add_row(c, row, "Response Access Token Field:", self._access_field); row += 1

        self._username_claim = JTextField("username")
        self._add_row(c, row, "JWT Username Claim:", self._username_claim); row += 1

        self._auth_header_name = JTextField("Authorization")
        self._add_row(c, row, "Auth Header Name:", self._auth_header_name); row += 1

        self._fail_codes = JTextField("401,403")
        self._add_row(c, row, "Refresh On Status Codes:", self._fail_codes); row += 1

        self._preemptive_enabled = JCheckBox("Enable pre-emptive refresh (sync when near expiry)", True)
        c.gridx = 0; c.gridy = row; c.gridwidth = 2
        self._panel.add(self._preemptive_enabled, c)
        row += 1

        self._skew_seconds = JTextField("10")
        self._add_row(c, row, "Pre-emptive skew seconds (exp <= now + skew):", self._skew_seconds); row += 1

        self._enabled = JCheckBox("Enable extension", True)
        c.gridx = 0; c.gridy = row; c.gridwidth = 2
        self._panel.add(self._enabled, c)
        row += 1

        self._mapping = JTextArea(8, 60)
        self._mapping.setText('{\n  "alice": "refresh_alice_123",\n  "bob": "refresh_bob_456"\n}\n')
        scroll = JScrollPane(self._mapping)

        c.gridx = 0; c.gridy = row; c.gridwidth = 2
        self._panel.add(JLabel("Username -> Refresh Token Mapping (JSON):"), c)
        row += 1

        c.gridx = 0; c.gridy = row; c.gridwidth = 2
        c.fill = GridBagConstraints.BOTH
        c.weighty = 1.0
        self._panel.add(scroll, c)
        c.fill = GridBagConstraints.HORIZONTAL
        c.weighty = 0.0
        row += 1

        self._test_btn = JButton("Test Parse Mapping", actionPerformed=self._on_test_mapping)
        self._clear_btn = JButton("Clear Cached Access Tokens", actionPerformed=self._on_clear_cache)

        btn_panel = JPanel()
        btn_panel.add(self._test_btn)
        btn_panel.add(self._clear_btn)

        c.gridx = 0; c.gridy = row; c.gridwidth = 2
        self._panel.add(btn_panel, c)

        callbacks.addSuiteTab(self)
        callbacks.registerHttpListener(self)

        self._callbacks.printOutput("[+] Extension loaded.")

    # ----- ITab -----
    def getTabCaption(self):
        return "JWT Refresh"

    def getUiComponent(self):
        return self._main

    # ----- IHttpListener -----
    def processHttpMessage(self, toolFlag, messageIsRequest, messageInfo):
        if not self._enabled.isSelected():
            return
        try:
            if messageIsRequest:
                self._handle_request(messageInfo)
            else:
                self._handle_response(messageInfo)
        except Exception as e:
            self._callbacks.printError("Error: %s" % str(e))

    # -------------------------
    # Request hook
    # -------------------------
    def _handle_request(self, messageInfo):
        req = messageInfo.getRequest()
        info = self._helpers.analyzeRequest(messageInfo.getHttpService(), req)
        headers = list(info.getHeaders())
        body = req[info.getBodyOffset():]

        auth_name = self._auth_header_name.getText().strip()
        token = self._extract_bearer_from_headers(headers, auth_name)
        if not token:
            return

        meta = self._get_token_meta_cached(token)
        username = meta.get("username")
        exp_epoch = meta.get("exp")
        if not username:
            return

        # 1) If token is near expiry, refresh SYNCHRONOUSLY so THIS request can succeed.
        if self._preemptive_enabled.isSelected() and self._should_preemptive_refresh(exp_epoch):
            rt = self._get_refresh_token_for_user(username)
            if rt:
                # We intentionally do NOT use async refresh here, because we want immediate replacement.
                new_access = self._refresh_access_token(rt)
                if new_access:
                    self._lock.lock()
                    try:
                        self._token_by_username[username] = new_access
                    finally:
                        self._lock.unlock()
                    # Also cache meta for the new token lazily when first seen; nothing required here.
                    token = new_access  # use it immediately for this request
                    headers = self._replace_bearer_in_headers(headers, auth_name, new_access)
                    new_req = self._helpers.buildHttpMessage(headers, body)
                    messageInfo.setRequest(new_req)
                    return
                # If refresh fails, fall through: we may still inject an already cached token.

        # 2) Otherwise, inject newest cached token if it exists
        self._lock.lock()
        try:
            cached = self._token_by_username.get(username)
        finally:
            self._lock.unlock()

        if cached and cached != token:
            new_headers = self._replace_bearer_in_headers(headers, auth_name, cached)
            new_req = self._helpers.buildHttpMessage(new_headers, body)
            messageInfo.setRequest(new_req)

    # -------------------------
    # Response hook (async refresh on 401/403)
    # -------------------------
    def _handle_response(self, messageInfo):
        resp = messageInfo.getResponse()
        if resp is None:
            return

        resp_info = self._helpers.analyzeResponse(resp)
        status = resp_info.getStatusCode()

        fail_set = self._parse_fail_codes(self._fail_codes.getText())
        if status not in fail_set:
            return

        req = messageInfo.getRequest()
        req_info = self._helpers.analyzeRequest(messageInfo.getHttpService(), req)
        headers = list(req_info.getHeaders())

        auth_name = self._auth_header_name.getText().strip()
        token = self._extract_bearer_from_headers(headers, auth_name)
        if not token:
            return

        meta = self._get_token_meta_cached(token)
        username = meta.get("username")
        if not username:
            return

        refresh_token = self._get_refresh_token_for_user(username)
        if not refresh_token:
            self._callbacks.printError("No refresh token found for user '%s'." % username)
            return

        # Stampede protection
        self._lock.lock()
        try:
            if username in self._refreshing_user:
                return
            self._refreshing_user.add(username)
        finally:
            self._lock.unlock()

        def run_refresh():
            try:
                new_access = self._refresh_access_token(refresh_token)
                if new_access:
                    self._lock.lock()
                    try:
                        self._token_by_username[username] = new_access
                    finally:
                        self._lock.unlock()
                    self._callbacks.printOutput("[+] Refreshed token for user '%s' (trigger %d)." % (username, status))
                else:
                    self._callbacks.printError("[-] Refresh failed for user '%s'." % username)
            finally:
                self._lock.lock()
                try:
                    if username in self._refreshing_user:
                        self._refreshing_user.remove(username)
                finally:
                    self._lock.unlock()

        Thread(_Runnable(run_refresh)).start()

    # -------------------------
    # Refresh HTTP call
    # -------------------------
    def _refresh_access_token(self, refresh_token):
        refresh_url = self._refresh_url.getText().strip()
        method = self._refresh_method.getText().strip().upper()
        body_tmpl = self._body_template.getText()
        ctype = self._content_type.getText().strip()
        access_field = self._access_field.getText().strip()

        if not refresh_url:
            self._callbacks.printError("Refresh URL is empty.")
            return None

        body = body_tmpl.replace("{refresh_token}", self._json_escape(refresh_token))
        body_bytes = body.encode("utf-8")

        try:
            u = URL(refresh_url)
            host = u.getHost()
            protocol = (u.getProtocol() or "").lower()
            is_https = (protocol == "https")

            port = u.getPort()
            if port == -1:
                port = 443 if is_https else 80

            path = u.getFile()  # path + optional ?query
            if not path:
                path = "/"

            service = self._helpers.buildHttpService(host, port, is_https)

            headers = [
                "%s %s HTTP/1.1" % (method, path),
                "Host: %s" % host,
                "Content-Type: %s" % ctype,
                "Accept: application/json",
                "Connection: close",
            ]

            req = self._helpers.buildHttpMessage(headers, body_bytes)
            resp = self._callbacks.makeHttpRequest(service, req).getResponse()
            if resp is None:
                return None

            resp_info = self._helpers.analyzeResponse(resp)
            rbody = resp[resp_info.getBodyOffset():]
            text = self._helpers.bytesToString(rbody)

            return self._extract_access_token_from_json(text, access_field)

        except Exception as e:
            self._callbacks.printError("Refresh exception: %s" % str(e))
            return None

    # -------------------------
    # Token meta caching
    # -------------------------
    def _now_epoch(self):
        try:
            return int(System.currentTimeMillis() / 1000)
        except:
            return 0

    def _get_skew_seconds(self):
        try:
            return int(self._skew_seconds.getText().strip())
        except:
            return 10

    def _should_preemptive_refresh(self, exp_epoch):
        if exp_epoch is None:
            return False
        now = self._now_epoch()
        skew = self._get_skew_seconds()
        return exp_epoch <= (now + skew)

    def _get_token_meta_cached(self, jwt_token):
        if jwt_token in self._token_meta:
            return self._token_meta[jwt_token]

        meta = {"username": None, "exp": None}

        try:
            parts = jwt_token.split(".")
            if len(parts) >= 2:
                payload_json = self._b64url_decode_to_str(parts[1])
                if payload_json:
                    obj = self._parse_json(payload_json) or {}

                    claim = self._username_claim.getText().strip()
                    if claim in obj:
                        meta["username"] = str(obj.get(claim))
                    else:
                        for k in ["preferred_username", "user", "sub", "email", "upn"]:
                            if k in obj:
                                meta["username"] = str(obj.get(k))
                                break

                    if "exp" in obj:
                        try:
                            meta["exp"] = int(obj.get("exp"))
                        except:
                            meta["exp"] = None
        except:
            pass

        if len(self._token_meta) >= self._token_meta_max:
            self._token_meta.clear()

        self._token_meta[jwt_token] = meta
        return meta

    # -------------------------
    # Mapping parsing
    # -------------------------
    def _get_refresh_token_for_user(self, username):
        m = self._parse_mapping_json()
        if not m:
            return None
        if username in m:
            return str(m.get(username))
        return None

    def _parse_mapping_json(self):
        raw = self._mapping.getText().strip()
        if not raw:
            return None
        return self._parse_json(raw)

    # -------------------------
    # Header helpers
    # -------------------------
    def _extract_bearer_from_headers(self, headers, header_name):
        hn = header_name.lower()
        for h in headers:
            if h.lower().startswith(hn + ":"):
                val = h.split(":", 1)[1].strip()
                if val.lower().startswith("bearer "):
                    return val[7:].strip()
        return None

    def _replace_bearer_in_headers(self, headers, header_name, new_token):
        hn = header_name.lower()
        out = []
        replaced = False
        for h in headers:
            if h.lower().startswith(hn + ":"):
                out.append("%s: Bearer %s" % (header_name, new_token))
                replaced = True
            else:
                out.append(h)
        if not replaced:
            out.append("%s: Bearer %s" % (header_name, new_token))
        return out

    def _parse_fail_codes(self, s):
        out = set([401, 403])
        try:
            parts = [p.strip() for p in s.split(",") if p.strip()]
            out = set([int(p) for p in parts])
        except:
            pass
        return out

    # -------------------------
    # JSON helpers
    # -------------------------
    def _extract_access_token_from_json(self, text, field):
        obj = self._parse_json(text)
        if not obj:
            return None
        if field in obj:
            return str(obj.get(field))
        for k in ["accessToken", "token", "jwt", "id_token"]:
            if k in obj:
                return str(obj.get(k))
        return None

    def _parse_json(self, text):
        try:
            obj = json.loads(text)
            if isinstance(obj, dict):
                return obj
            return None
        except Exception as e:
            try:
                self._callbacks.printError("JSON parse error: %s" % str(e))
            except:
                pass
            return None

    def _json_escape(self, s):
        return str(s).replace("\\", "\\\\").replace('"', '\\"')

    # -------------------------
    # Base64url helper
    # -------------------------
    def _b64url_decode_to_str(self, data):
        s = data
        rem = len(s) % 4
        if rem == 2:
            s += "=="
        elif rem == 3:
            s += "="
        elif rem != 0:
            return None
        try:
            decoded = Base64.getUrlDecoder().decode(s)
            return self._helpers.bytesToString(decoded)
        except:
            return None

    # -------------------------
    # UI helpers
    # -------------------------
    def _add_row(self, c, row, label, comp):
        c.gridx = 0; c.gridy = row; c.gridwidth = 1; c.weightx = 0.0
        self._panel.add(JLabel(label), c)
        c.gridx = 1; c.gridy = row; c.gridwidth = 1; c.weightx = 1.0
        self._panel.add(comp, c)

    def _on_test_mapping(self, event):
        m = self._parse_mapping_json()
        if m is None:
            self._callbacks.printError("Mapping JSON parse failed.")
        else:
            try:
                keys = sorted(m.keys())
            except:
                keys = m.keys()
            self._callbacks.printOutput("[+] Mapping JSON OK. Users: %s" % ", ".join(keys))

    def _on_clear_cache(self, event):
        self._lock.lock()
        try:
            self._token_by_username.clear()
            self._token_meta.clear()
        finally:
            self._lock.unlock()
        self._callbacks.printOutput("[+] Cleared cached access tokens and token meta cache.")
