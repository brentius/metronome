"""HTTPS client for the project's RunPod flow pod (RunPod proxy -> token-protected Jupyter Server on port 8888).

Why HTTPS: this laptop's network filter blocks SSH (ssh.runpod.io:22 unreachable, checked 2026-11-11) but HTTPS to
*.proxy.runpod.net works. Ported from the ns-accel project's podctl.py (BOTS/PLANS/RUNPOD.md there).

Usage (from the repository root):
  python code/flow/runpod/podctl.py run  "<shell cmd>" [--timeout S]  run in a fresh terminal; exit with its status
  python code/flow/runpod/podctl.py bg   "<shell cmd>" LOGFILE         detach with nohup; output to LOGFILE (pod path)
  python code/flow/runpod/podctl.py put  LOCAL REMOTE                   upload a file (REMOTE relative to /workspace)
  python code/flow/runpod/podctl.py get  REMOTE LOCAL                   download a file
  python code/flow/runpod/podctl.py pack OUT.tgz PATH...                tar.gz of repo paths with CRLF -> LF for text
  python code/flow/runpod/podctl.py ping                                check the server answers

Env: JSC_POD = pod id. Token: ~/.jsc/jupyter_token (outside the repo, never committed).
From Git Bash, export MSYS_NO_PATHCONV=1 first, or MSYS rewrites "/workspace/..." arguments into Windows paths.
Cloudflare rejects the default Python User-Agent, so every request sets its own.
"""
from __future__ import annotations

import base64
import io
import json
import os
import re
import sys
import tarfile
import time
import urllib.error
import urllib.request
from pathlib import Path

UA = "jsc-podctl/1.0"
TEXT = {".sh", ".tcl", ".mk", ".sdc", ".py", ".v", ".sv", ".svh", ".vh", ".md", ".yaml", ".yml", ".json", ".txt",
        ".cfg", ".toml", ".lef", ".lib"}
SKIP = {"sim_build", "__pycache__", ".pytest_cache", ".git"}


def _cfg():
    pod = os.environ.get("JSC_POD")
    if not pod:
        sys.exit("set JSC_POD to the pod id")
    token = (Path.home() / ".jsc" / "jupyter_token").read_text().strip()
    return pod, token


def _req(method: str, path: str, body=None, timeout=120, retries=3):
    pod, token = _cfg()
    data = None if body is None else json.dumps(body).encode()
    hdr = {"Authorization": f"token {token}", "Content-Type": "application/json", "User-Agent": UA}
    for i in range(retries):
        try:
            r = urllib.request.Request(f"https://{pod}-8888.proxy.runpod.net{path}", data=data, method=method,
                                       headers=hdr)
            with urllib.request.urlopen(r, timeout=timeout) as f:
                txt = f.read()
            return json.loads(txt) if txt else None
        except urllib.error.HTTPError as e:
            if e.code < 500 or i == retries - 1:
                raise
        except (urllib.error.URLError, TimeoutError):
            if i == retries - 1:
                raise
        time.sleep(3 * (i + 1))


def _jpath(remote: str) -> str:
    """Jupyter contents paths are relative to its root (/workspace); accept absolute /workspace/... too."""
    r = remote.strip("/")
    return r[len("workspace/"):] if r.startswith("workspace/") else r


def put(local: str, remote: str):
    remote = _jpath(remote)
    parts = remote.split("/")
    for i in range(1, len(parts)):
        try:
            _req("PUT", f"/api/contents/{'/'.join(parts[:i])}", {"type": "directory"}, retries=1)
        except urllib.error.HTTPError:
            pass
    b = Path(local).read_bytes()
    if Path(local).suffix in TEXT or Path(local).name == "Makefile":
        b = b.replace(b"\r\n", b"\n")  # Windows checkout is CRLF; bash on the pod fails on CRLF scripts
    _req("PUT", f"/api/contents/{remote.strip('/')}",
         {"type": "file", "format": "base64", "content": base64.b64encode(b).decode()}, timeout=900)


def get(remote: str, local: str):
    remote = _jpath(remote)
    m = _req("GET", f"/api/contents/{remote.strip('/')}?content=1&format=base64&type=file", timeout=900)
    Path(local).parent.mkdir(parents=True, exist_ok=True)
    Path(local).write_bytes(base64.b64decode(m["content"]))


def run(cmd: str, timeout: float = 3600) -> int:
    import websocket  # websocket-client
    pod, token = _cfg()
    name = _req("POST", "/api/terminals")["name"]
    ws = websocket.create_connection(f"wss://{pod}-8888.proxy.runpod.net/terminals/websocket/{name}?token={token}",
                                     timeout=60, header=[f"User-Agent: {UA}"])
    tag = f"__JSC_{int(time.time() * 1000)}__"
    ws.send(json.dumps(["stdin", f"stty -echo; {cmd}; echo {tag}$?\r"]))
    out, t0 = "", time.time()
    pat = re.compile(re.escape(tag) + r"(\d+)")
    try:
        while time.time() - t0 < timeout:
            try:
                msg = json.loads(ws.recv())
            except websocket.WebSocketTimeoutException:
                continue
            if msg[0] == "stdout":
                out += msg[1]
                m = pat.search(out)
                chunk = msg[1] if not m else msg[1].split(tag)[0]
                sys.stdout.write(chunk)
                sys.stdout.flush()
                if m:
                    return int(m.group(1))
        print(f"\n[podctl] timeout after {timeout}s (remote command may still run)", file=sys.stderr)
        return 124
    finally:
        ws.close()
        try:
            _req("DELETE", f"/api/terminals/{name}", retries=1)
        except Exception:
            pass


def pack(out: str, paths: list[str]) -> int:
    n = 0
    with tarfile.open(out, "w:gz") as t:
        for r in paths:
            rp = Path(r)
            files = [rp] if rp.is_file() else sorted(rp.rglob("*"))
            for p in files:
                if p.is_dir() or any(x in SKIP for x in p.parts) or p.suffix in {".vcd", ".fst", ".vvp"}:
                    continue
                b = p.read_bytes()
                if p.suffix in TEXT or p.name in {"Makefile"}:
                    b = b.replace(b"\r\n", b"\n")
                ti = tarfile.TarInfo(p.as_posix())
                ti.size, ti.mtime = len(b), int(p.stat().st_mtime)
                ti.mode = 0o755 if p.suffix in {".sh", ".py"} else 0o644
                t.addfile(ti, io.BytesIO(b))
                n += 1
    return n


def main() -> int:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")  # Windows console is cp1252
    a = sys.argv[1:]
    if not a:
        print(__doc__)
        return 2
    if a[0] == "run":
        return run(a[1], float(a[a.index("--timeout") + 1]) if "--timeout" in a else 3600)
    if a[0] == "bg":
        # New session so the job survives the terminal being deleted (terminado signals the process group).
        spawn = ("import os,subprocess,sys; os.makedirs(os.path.dirname(sys.argv[2]),exist_ok=True); "
                 "p=subprocess.Popen(['bash','-c',sys.argv[1]],stdout=open(sys.argv[2],'ab'),"
                 "stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,start_new_session=True); print('BG_PID',p.pid)")
        q = lambda s: "'" + s.replace("'", "'\"'\"'") + "'"  # noqa: E731  shell single-quote
        return run(f"python3 -c {q(spawn)} {q(a[1])} {q(a[2])}", 60)
    if a[0] == "put":
        put(a[1], a[2])
        return 0
    if a[0] == "get":
        get(a[1], a[2])
        return 0
    if a[0] == "pack":
        print(a[1], pack(a[1], a[2:]))
        return 0
    if a[0] == "ping":
        print(_req("GET", "/api/status"))
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
