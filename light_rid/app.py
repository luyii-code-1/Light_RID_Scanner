from __future__ import annotations

from .runtime import RuntimeContext, create_runtime_context, load_namespace


def _packager_import_anchor() -> None:
    # pylint: disable=import-outside-toplevel,unused-import,unused-variable,import-error
    # PyInstaller cannot see imports inside the legacy chunks loaded by exec().
    # Keep this uncalled anchor until those chunks become normal modules.
    import argparse
    import base64
    import curses
    import difflib
    import grp
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
    import pwd
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
    from scapy.all import Dot11, Dot11Beacon, Dot11Elt, RadioTap, conf, sniff

    return None


def main(ctx: RuntimeContext | None = None) -> None:
    runtime_ctx = ctx or create_runtime_context()
    load_namespace(runtime_ctx)["main"]()
