"""Application bootstrap for the assembled Light RID runtime."""

from __future__ import annotations

from .runtime import RuntimeContext, create_runtime_context, load_namespace


def _packager_import_anchor() -> None:
    """Expose dynamic runtime imports to packagers without executing scanner code."""
    # pylint: disable=import-outside-toplevel,unused-import,unused-variable
    # PyInstaller cannot see imports inside the legacy chunks loaded by exec().
    # Keep this uncalled anchor until those chunks become normal modules.
    import argparse
    import base64
    import curses
    import difflib
    import hashlib
    import hmac
    import http.server
    import io
    import ipaddress
    import json
    import logging
    import math
    import os
    import platform
    import queue
    import random
    import re
    import secrets
    import shlex
    import shutil
    import socket
    import socketserver
    import struct
    import subprocess
    import sys
    import tempfile
    import threading
    import time
    import urllib.error
    import urllib.parse
    import urllib.request
    import zipfile
    import zlib
    from collections import deque
    from threading import Lock, Thread
    from station_edition.light_rid import analize_core
    from station_edition.light_rid import platform_compat
    from scapy.config import conf
    from scapy.layers.dot11 import Dot11, Dot11Beacon, Dot11Elt, RadioTap
    from scapy.sendrecv import sniff


def main(ctx: RuntimeContext | None = None) -> None:
    """Load the assembled scanner namespace and run its main function."""
    runtime_ctx = ctx or create_runtime_context()
    load_namespace(runtime_ctx)["main"]()
