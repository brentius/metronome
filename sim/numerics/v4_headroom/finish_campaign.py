"""Finish existing v4p1 probes and publish an archive-verification DONE marker.

Runs on the pod; no lifecycle credentials or stop action. At the conservative
cutoff it suspends validated tt_tool harden launchers and their descendants,
then archives that interrupted state. DONE means selected archives verified,
never physical success. The external controller audits gates and handles MCP stop.
"""
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tarfile
import time

OUT = Path('/workspace/archives/v4_phase1_final_20261117')
CUTOFF = dt.datetime(2026, 11, 18, 5, 40, tzinfo=dt.timezone.utc)
PRECHECK_DEADLINE = dt.datetime(2026, 11, 18, 5, 50, tzinfo=dt.timezone.utc)
TAGS = sorted(p.name for p in Path('/workspace/results').glob('v4p1_b*'))
OUT.mkdir(exist_ok=True)
if any(OUT.iterdir()):
    raise RuntimeError('refusing to overwrite existing archive outputs')

# Replace only the previous waiting archiver, never a physical-flow process.
for proc in Path('/proc').glob('[0-9]*'):
    try:
        argv = (proc / 'cmdline').read_bytes().split(b'\0')
        if (b'/workspace/jsc/recovery_archive.py' in argv
                or (b'/workspace/jsc/finish_campaign.py' in argv
                    and int(proc.name) != os.getpid())):
            os.kill(int(proc.name), signal.SIGTERM)
    except (FileNotFoundError, PermissionError, ProcessLookupError):
        pass


def digest(path):
    with open(path, 'rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def exits():
    text = Path('/workspace/results/runs.log').read_text()
    return {t: int(m.group(1)) for t in TAGS
            if (m := re.search(r'^\S+ ' + re.escape(t) + r' rc=(\d+) ', text, re.M))}


while True:
    rc = exits()
    pending = [t for t in TAGS if t not in rc]
    print(dt.datetime.now(dt.timezone.utc).isoformat(), 'pending', pending, flush=True)
    if not pending or dt.datetime.now(dt.timezone.utc) >= CUTOFF:
        break
    time.sleep(45)

suspended = []
if pending:
    roots = [Path('/root/work') / t for t in pending]
    owned = set()
    # Stop launchers first, then rescan their descendants so no new flow
    # children can be launched during capture. Cwd alone is never ownership.
    for iteration in range(2):
        rows = {}
        for proc in Path('/proc').glob('[0-9]*'):
            try:
                stat = (proc / 'stat').read_text().rsplit(')', 1)[1].split()
                rows[int(proc.name)] = {
                    'ppid': int(stat[1]), 'start': stat[19],
                    'argv': (proc / 'cmdline').read_bytes().split(b'\0'),
                    'cwd': (proc / 'cwd').resolve(strict=True)}
            except (FileNotFoundError, PermissionError, ProcessLookupError):
                pass
        for pid, row in rows.items():
            if (row['cwd'] in roots and b'./tt/tt_tool.py' in row['argv']
                    and b'--harden' in row['argv']):
                owned.add(pid)
        changed = True
        while changed:
            before = len(owned)
            owned.update(pid for pid, row in rows.items() if row['ppid'] in owned)
            changed = len(owned) != before
        for pid in sorted(owned):
            if pid not in rows:
                continue
            proc = Path('/proc') / str(pid)
            try:
                now = (proc / 'stat').read_text().rsplit(')', 1)[1].split()
                if now[19] != rows[pid]['start']:
                    raise RuntimeError('PID identity changed before suspension')
                os.kill(pid, signal.SIGSTOP)
                suspended.append({'pid': pid, 'cwd': str(rows[pid]['cwd']),
                                  'start_ticks': rows[pid]['start']})
            except (FileNotFoundError, ProcessLookupError):
                pass  # Exited before suspension; no live writer remains.
        time.sleep(1)
    time.sleep(2)

completion = {'exit_codes': rc, 'unfinished_at_cutoff': pending,
              'suspended': suspended, 'cutoff_utc': CUTOFF.isoformat()}
(OUT / 'completion.json').write_text(json.dumps(completion, indent=2))

for tag in TAGS:
    with open(OUT / (tag + '.collect.log'), 'w') as log:
        code = subprocess.run(['python3', '/workspace/jsc/collect_recovery.py', tag],
                              stdout=log, stderr=subprocess.STDOUT).returncode
    completion.setdefault('collector_exit_codes', {})[tag] = code

# Precheck only complete timing-clean runs. Serialize because tt_precheck.sh
# uses one shared /root/tt/precheck/reports directory.
for tag, code in rc.items():
    res = Path('/workspace/results') / tag
    summary = res / 'v4p1_summary.json'
    if code == 0 and summary.exists():
        data = json.loads(summary.read_text())
        if data.get('timing_closed_all_corners') and not (res / 'precheck').exists():
            available = (PRECHECK_DEADLINE - dt.datetime.now(dt.timezone.utc)).total_seconds()
            if available < 60:
                completion.setdefault('precheck_exit_codes', {})[tag] = 'not run: archival deadline'
                continue
            with open(OUT / (tag + '.precheck_launcher.log'), 'w') as log:
                pre = subprocess.Popen(['bash', '/workspace/jsc/flow/tt_precheck.sh', tag],
                                       stdout=log, stderr=subprocess.STDOUT,
                                       start_new_session=True)
                try:
                    code = pre.wait(timeout=min(1800, available))
                    completion.setdefault('precheck_exit_codes', {})[tag] = code
                except subprocess.TimeoutExpired:
                    os.killpg(pre.pid, signal.SIGTERM)
                    try:
                        pre.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        os.killpg(pre.pid, signal.SIGKILL)
                        pre.wait()
                    completion.setdefault('precheck_exit_codes', {})[tag] = 'timeout'
(OUT / 'completion.json').write_text(json.dumps(completion, indent=2))

roots = (list(Path('/root/work').glob('v4*'))
         + list(Path('/workspace/results').glob('v4p1*'))
         + list(Path('/workspace/jsc/upload').glob('v4p1*'))
         + list(Path('/workspace/jobs').glob('v4p1*'))
         + list(Path('/workspace/jsc').glob('*v4*'))
         + list(Path('/workspace/jsc').glob('recovery*'))
         + list(Path('/workspace/jobs').glob('v4_recovery*'))
         + list(OUT.glob('*.log'))
         + [Path('/root/e0'), Path('/root/flow_versions.txt'),
            Path('/workspace/archives/v4_phase1_recovery_20261117'),
            Path('/workspace/results/runs.log'),
            Path('/workspace/jsc/collect_recovery.py'),
            Path('/workspace/jsc/finish_campaign.py'),
            OUT / 'completion.json'])
files = {str(f).lstrip('/'): f for root in roots if root.exists()
         for f in ([root] if root.is_file() else root.rglob('*')) if f.is_file()}
manifest = {name: {'size': f.stat().st_size, 'sha256': digest(f)}
            for name, f in sorted(files.items())}
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=1))


def archive_verified(name, selected):
    archive = OUT / name
    # File symlinks are dereferenced deliberately; directory symlinks are not
    # traversed by rglob. Every manifested member must be a regular byte stream.
    with tarfile.open(archive, 'w:gz', compresslevel=3, dereference=True) as tar:
        for key in sorted(selected):
            tar.add(files[key], arcname=key, recursive=False)
    actual = {}
    with tarfile.open(archive) as tar:
        for member in tar:
            assert member.isfile(), member.name
            assert member.name not in actual, member.name
            with tar.extractfile(member) as stream:
                actual[member.name] = {'size': member.size,
                    'sha256': hashlib.file_digest(stream, 'sha256').hexdigest()}
    expected = {key: manifest[key] for key in selected}
    assert actual == expected, 'archive member/size/hash mismatch'
    return {'archive': str(archive), 'bytes': archive.stat().st_size,
            'sha256': digest(archive), 'verified_members': len(actual)}


records = {'native': archive_verified('all_native.tgz', files),
           'results': archive_verified('results.tgz', [k for k in files
                if not k.startswith('root/work/')]),
           'roots': [str(r) for r in roots],
           'symlink_policy': 'file targets copied; directory symlinks not traversed',
           'marker_meaning': 'selected archives hash-verified; NOT physical success',
           'collection_complete': all(v == 0 for v in completion['collector_exit_codes'].values()),
           'physical_exit_codes': rc, 'unfinished_at_cutoff': pending,
           'completed_utc': dt.datetime.now(dt.timezone.utc).isoformat()}
(OUT / 'verification.json').write_text(json.dumps(records, indent=2))
(OUT / 'DONE').write_text(records['completed_utc'] + '\n')
print(json.dumps(records), flush=True)
