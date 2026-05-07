from __future__ import annotations

from pathlib import Path
import sys

_CHUNK_FILES = (
    "common_core.py",
    "hardware_core.py",
    "scan_core.py",
    "process_core.py",
    "auth_core.py",
    "web_server.py",
    "cli_app.py",
)

_LOADED = False

# The legacy runtime was one file with shared globals. During the first split we
# keep one namespace so behavior remains stable while the physical source is
# separated by responsibility.
_NAMESPACE = {
    "__name__": "light_rid._assembled",
    "__package__": "light_rid",
    "__file__": str(Path(sys.argv[0]).resolve()),
}


def _package_dir() -> Path:
    return Path(__file__).resolve().parent


def _chunk_path(name: str) -> Path:
    return _package_dir() / name


def load_namespace() -> dict:
    global _LOADED
    if _LOADED:
        return _NAMESPACE
    for name in _CHUNK_FILES:
        path = _chunk_path(name)
        source = path.read_text(encoding="utf-8")
        exec(compile(source, str(path), "exec"), _NAMESPACE)
    _LOADED = True
    return _NAMESPACE