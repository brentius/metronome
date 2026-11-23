"""Download the pinned third-party device models into build/vendor/ and verify SHA-256.

    python -I code/tests/vendor_models/fetch_vendor.py

Downloads are untrusted data: only Verilog source/data files are fetched, nothing from them is executed.
Hashes are of the raw upstream bytes; a CRLF-converted copy is accepted when it matches after normalising.
"""
import hashlib
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
VENDOR = ROOT / "build" / "vendor"

W25 = ("lijiaxun-sgms/w25q128jvxim_v_sim", "6cfed424e0426bb1156f718259d3ce2667b98a65")
AK = ("azonenberg/antikernel", "6c2915428b897b596694419b428202e9b5273b80")

# (dest under build/vendor, repo, commit, path in repo, sha256 of upstream bytes)
FILES = [
    ("w25q128jv/W25Q128JVxIM.v", *W25, "W25Q128JVxIM.v", "625495dcd898c6042b3adfb8ed1de3c77a8d58acda532a15a67b1dc9ba02efcd"),
    ("w25q128jv/LICENSE", *W25, "LICENSE", "6b0382b16279f26ff69014300541967a356a666eb0b91b422f6862f6b7dad17e"),
    ("w25q128jv/SFDP.TXT", *W25, "SFDP.TXT",
     "73d55352d9a73285d9d441cc5a9635fb9cfb2266f646f85023c7dbde9f9ecbe5"),
    ("w25q128jv/SECSI.TXT", *W25, "SECSI.TXT",
     "83bf735a69c5f3c279a577e6c2a99e6de60d897a79ba4708e56790dd6b80489a"),
    ("w25q128jv/SREG.TXT", *W25, "SREG.TXT",
     "3fd2178f2da76bee4b5c6ca7e03ef0ed59e67d7fe112905bc99fd246be458ed8"),
    ("antikernel/models/i2c_eeprom/24LC256.v", *AK, "legacy-trunk/3rdparty/models/i2c_eeprom/24LC256.v",
     "d403d5325b5625c4de8517881ad0ceff60fd80a42131c894beda871d470ad0a9"),
]


def sha(b, want=None):
    """Raw-byte hash, or the LF-normalised hash when that is what is pinned (CRLF-converted copies)."""
    raw = hashlib.sha256(b).hexdigest()
    return raw if want in (None, raw) else hashlib.sha256(b.replace(bytes([13,10]), bytes([10]))).hexdigest()


def main():
    bad = 0
    for dest, repo, commit, path, want in FILES:
        p = VENDOR / dest
        if not p.exists():
            url = f"https://raw.githubusercontent.com/{repo}/{commit}/{path}"
            data = urllib.request.urlopen(url, timeout=60).read()
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(data)
        got = sha(p.read_bytes(), want)
        ok = want is None or got == want
        bad += not ok
        print(("ok  " if ok else "BAD ") + dest, got)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
