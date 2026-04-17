#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Servidor MCP de prueba - network.checkResonance (Nivel B)."""

import json
import os
import sys
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path


def _check_node_resonance(node: str) -> dict:
    project_root = Path(__file__).resolve().parent.parent
    if str(project_root) not in sys.path:
        sys.path.insert(0, str(project_root))
    from mcp_network.resonance import check_node_resonance

    return check_node_resonance(node)


class MCPTestHandler(BaseHTTPRequestHandler):
    """Minimal JSON-RPC server for resonance checks."""

    def _send_json(self, payload: dict, status: int = 200) -> None:
        encoded = json.dumps(payload).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(encoded)))
        self.end_headers()
        self.wfile.write(encoded)

    def do_POST(self):
        # BaseHTTPRequestHandler requires this method name for POST handlers.
        if self.path != "/jsonrpc":
            self.send_error(404)
            return

        content_length = self.headers.get("Content-Length")
        if content_length is None:
            self._send_json(
                {"jsonrpc": "2.0", "id": None, "error": {"code": -32600, "message": "Invalid Request"}}
            )
            return

        try:
            raw = self.rfile.read(int(content_length))
            request = json.loads(raw)
        except (ValueError, json.JSONDecodeError):
            self._send_json(
                {"jsonrpc": "2.0", "id": None, "error": {"code": -32700, "message": "Parse error"}}
            )
            return

        if not isinstance(request, dict):
            self._send_json(
                {"jsonrpc": "2.0", "id": None, "error": {"code": -32600, "message": "Invalid Request"}}
            )
            return

        if request.get("method") == "network.checkResonance":
            node = request.get("params", {}).get("node", "")
            response = {
                "jsonrpc": "2.0",
                "id": request.get("id"),
                "result": _check_node_resonance(node),
            }
        else:
            response = {
                "jsonrpc": "2.0",
                "id": request.get("id"),
                "error": {"code": -32601, "message": "Method not found"},
            }

        self._send_json(response)


if __name__ == "__main__":
    port = int(os.getenv("MCP_TEST_PORT", "8506"))
    server = HTTPServer(("127.0.0.1", port), MCPTestHandler)
    print(f"🚀 MCP Test Server escuchando en http://127.0.0.1:{port}/jsonrpc")
    print("Método expuesto: network.checkResonance")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nServidor detenido.")
