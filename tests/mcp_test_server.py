#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Servidor MCP de prueba - network.checkResonance (Nivel B)."""

import json
from http.server import BaseHTTPRequestHandler, HTTPServer

from mcp_network.resonance import check_node_resonance


class MCPTestHandler(BaseHTTPRequestHandler):
    """Minimal JSON-RPC server for resonance checks."""

    def do_POST(self):
        if self.path != "/jsonrpc":
            self.send_error(404)
            return

        content_length = int(self.headers["Content-Length"])
        request = json.loads(self.rfile.read(content_length))

        if request.get("method") == "network.checkResonance":
            node = request.get("params", {}).get("node", "")
            response = {
                "jsonrpc": "2.0",
                "id": request.get("id"),
                "result": check_node_resonance(node),
            }
        else:
            response = {
                "jsonrpc": "2.0",
                "id": request.get("id"),
                "error": {"code": -32601, "message": "Method not found"},
            }

        payload = json.dumps(response).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)


if __name__ == "__main__":
    port = 8506
    server = HTTPServer(("127.0.0.1", port), MCPTestHandler)
    print(f"🚀 MCP Test Server escuchando en http://127.0.0.1:{port}/jsonrpc")
    print("Método expuesto: network.checkResonance")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nServidor detenido.")
