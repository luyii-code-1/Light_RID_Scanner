"""Runtime paths for source and PyInstaller viewer builds."""

from __future__ import annotations

import os
import sys
from pathlib import Path


APP_NAME = "Light RID Node Center"
APP_VERSION = "0.1.0"
DEFAULT_HOST = "0.0.0.0"
DEFAULT_PORT = 4700

if getattr(sys, "frozen", False):
    ROOT = Path(getattr(sys, "_MEIPASS", Path(sys.executable).resolve().parent))
    VIEWER_DIR = Path.cwd()
else:
    ROOT = Path(__file__).resolve().parent.parent
    VIEWER_DIR = Path(__file__).resolve().parent

DEFAULT_DB = Path(os.environ.get("LIGHT_RID_VIEWER_DB") or (VIEWER_DIR / "cfg.db"))
ASSETS_DIR = ROOT / "station_edition" / "light_rid" / "assets"
STATION_WEB_SERVER = ROOT / "station_edition" / "light_rid" / "web_server.py"
EULA_PATH = ROOT / "EULA.md"
