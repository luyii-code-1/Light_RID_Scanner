#!/usr/bin/env python3
"""Portable edition build wrapper."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from pytools.build_release import main


if __name__ == "__main__":
    sys.argv = [sys.argv[0], "--edition", "portable", *sys.argv[1:]]
    raise SystemExit(main())
