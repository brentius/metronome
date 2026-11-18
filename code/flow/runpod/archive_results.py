"""Archive past run directories in /workspace/results into one verified tar.zst, then delete the originals.

    archive_results.py NAME --exclude PREFIX [--exclude PREFIX ...] [--delete]

1. Hash every file of every selected entry (manifest NAME.manifest.json).
2. tar | gzip into /workspace/archives/NAME.tar.gz.
3. Re-read the archive and hash every member; the archive passes only if every manifest file is present with the
   same SHA-256 and size and nothing extra exists.
4. Only with --delete and a passing verification: remove the original entries. Record NAME.record.json.
"""
import argparse, hashlib, json, os, shutil, subprocess, sys, tarfile, time
R = "/workspace/results"; A = "/workspace/archives"
ap = argparse.ArgumentParser(); ap.add_argument("name"); ap.add_argument("--exclude", action="append", default=[])
ap.add_argument("--delete", action="store_true"); a = ap.parse_args()
os.makedirs(A, exist_ok=True)
arc, man, rec = f"{A}/{a.name}.tar.gz", f"{A}/{a.name}.manifest.json", f"{A}/{a.name}.record.json"
assert not os.path.exists(arc), arc
keep = ("runs.log",)
entries = sorted(e for e in os.listdir(R) if e not in keep and not any(e.startswith(x) for x in a.exclude))
print(time.strftime("%H:%M:%S"), "entries", len(entries), flush=True)

def h(fobj):
    d = hashlib.sha256(); n = 0
    for b in iter(lambda: fobj.read(1 << 20), b""): d.update(b); n += len(b)
    return d.hexdigest(), n

files = {}
for e in entries:
    p = os.path.join(R, e)
    walk = [(p, [], [e])] if os.path.isfile(p) else [(dp, None, fn) for dp, _, fn in os.walk(p)]
    for dp, _, fn in walk:
        for f in fn:
            fp = os.path.join(dp, f) if os.path.isdir(p) else p
            if os.path.islink(fp) or not os.path.isfile(fp): continue
            with open(fp, "rb") as fo: files[os.path.relpath(fp, R)] = h(fo)
json.dump({"entries": entries, "files": files}, open(man, "w"), indent=1)
print(time.strftime("%H:%M:%S"), "hashed", len(files), "bytes", sum(n for _, n in files.values()), flush=True)
tarp = subprocess.Popen(["tar", "-C", R, "-cf", "-", *entries], stdout=subprocess.PIPE)
with open(arc, "wb") as out:
    z = subprocess.run(["gzip", "-6", "-c"], stdin=tarp.stdout, stdout=out)
assert tarp.wait() == 0 and z.returncode == 0, "tar/zstd failed"
print(time.strftime("%H:%M:%S"), "archived", os.path.getsize(arc), flush=True)
dz = subprocess.Popen(["gzip", "-d", "-c", arc], stdout=subprocess.PIPE)
seen = {}
with tarfile.open(fileobj=dz.stdout, mode="r|") as t:
    for m in t:
        if m.isfile(): seen[m.name] = h(t.extractfile(m))
dz.wait()
bad = sorted(k for k in files if seen.get(k) != tuple(files[k]))
extra = sorted(set(seen) - set(files))
ok = not bad and not extra and dz.returncode == 0
r = {"archive": arc, "sha256": h(open(arc, "rb"))[0], "size": os.path.getsize(arc), "files": len(files),
     "verified": ok, "bad": bad[:50], "extra": extra[:50], "deleted": False, "time": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
if ok and a.delete:
    for e in entries:
        p = os.path.join(R, e); shutil.rmtree(p) if os.path.isdir(p) and not os.path.islink(p) else os.remove(p)
    r["deleted"] = True
json.dump(r, open(rec, "w"), indent=1); print("RECORD", json.dumps(r), flush=True)
sys.exit(0 if ok else 1)
