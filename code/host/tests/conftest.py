import sys
from pathlib import Path

HOST = Path(__file__).resolve().parents[1]
for p in (HOST, HOST.parent / "md", Path(__file__).resolve().parent):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))
