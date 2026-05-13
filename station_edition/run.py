"""Station edition entrypoint for Light RID Scanner."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from station_edition.light_rid.app import main


if __name__ == "__main__":
    main()
