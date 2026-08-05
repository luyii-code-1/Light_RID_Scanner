from __future__ import annotations

import json
import unittest
from pathlib import Path

from station_edition.light_rid.runtime import create_runtime_context, load_namespace


class _ChunkSocket:
    def __init__(self, data: bytes, chunk_size: int = 2) -> None:
        self.data = bytearray(data)
        self.chunk_size = chunk_size

    def recv(self, size: int) -> bytes:
        if not self.data:
            return b""
        count = min(size, self.chunk_size, len(self.data))
        chunk = bytes(self.data[:count])
        del self.data[:count]
        return chunk


class WebSocketRttTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.runtime = load_namespace(create_runtime_context())

    def test_masked_browser_ping_frame_is_decoded(self) -> None:
        payload = json.dumps({"kind": "ping", "id": "42"}, separators=(",", ":")).encode()
        mask = bytes((0x12, 0x34, 0x56, 0x78))
        masked = bytes(value ^ mask[index % 4] for index, value in enumerate(payload))
        frame = bytes((0x81, 0x80 | len(payload))) + mask + masked
        opcode, decoded = self.runtime["_ws_recv_client_frame"](_ChunkSocket(frame))
        self.assertEqual(opcode, 1)
        self.assertEqual(json.loads(decoded), {"kind": "ping", "id": "42"})

    def test_ui_uses_ping_pong_rtt_not_server_clock_age(self) -> None:
        source = Path("station_edition/light_rid/web_server.py").read_text(encoding="utf-8")
        self.assertIn("performance.now() - started", source)
        self.assertIn("JSON.stringify({kind:'ping', id:id})", source)
        self.assertIn('message.get("kind") == "ping"', source)
        self.assertNotIn("Date.now() - serverMs", source)


if __name__ == "__main__":
    unittest.main()
