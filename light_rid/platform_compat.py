"""Platform compatibility helpers for optional POSIX facilities."""

from __future__ import annotations

import importlib
import os
from types import ModuleType


def _optional_module(name: str) -> ModuleType | None:
    """Import an optional platform module without tripping static import checks."""
    try:
        return importlib.import_module(name)
    except ModuleNotFoundError:
        return None


def username_for_uid(uid: int | None) -> str:
    """Return a POSIX username for uid when the host supports pwd."""
    if uid is not None:
        pwd_mod = _optional_module("pwd")
        if pwd_mod is not None:
            try:
                return str(pwd_mod.getpwuid(int(uid)).pw_name or "")
            except (KeyError, OSError, TypeError, ValueError):
                pass
    return str(os.environ.get("USER") or os.environ.get("USERNAME") or "")


def local_user_exists(name: str) -> bool | None:
    """Return user existence from pwd, or None when pwd is unavailable."""
    user = str(name or "").strip()
    if not user:
        return False
    pwd_mod = _optional_module("pwd")
    if pwd_mod is None:
        return None
    try:
        pwd_mod.getpwnam(user)
        return True
    except KeyError:
        return False


def local_group_exists(name: str) -> bool | None:
    """Return group existence from grp, or None when grp is unavailable."""
    group = str(name or "").strip()
    if not group:
        return False
    grp_mod = _optional_module("grp")
    if grp_mod is None:
        return None
    try:
        grp_mod.getgrnam(group)
        return True
    except KeyError:
        return False
