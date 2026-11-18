"""Print the failing assertion and the symbolic payload/delay of a SymbiYosys BMC counterexample: ce_summary.py WORKDIR"""
import re, sys
w = sys.argv[1]
log = open(w + "/logfile.txt").read()
m = re.findall(r"failed assertion .*? at (\S+) step (\d+)", log)
print("failed:", m[-1] if m else "none (no failure)", "| result:", re.findall(r"DONE \((\w+)", log))
try:
    f = open(w + "/engine_0/trace.vcd").read().split("\n")
except OSError:
    sys.exit()
scope, ids = [], {}
for l in f:
    if l.startswith("$scope"): scope.append(l.split()[2])
    elif l.startswith("$upscope"): scope.pop()
    elif l.startswith("$var"):
        p = l.split(); ids.setdefault(p[3], []).append(".".join(scope + [p[4]]))
want = {i: n.split(".")[-1] for i, ns in ids.items() for n in ns if n in ("fv_uart_tx.payload", "fv_uart_tx.delay")}
cur = {}
for l in f:
    if l.startswith("b"):
        v, i = l[1:].split()
        if i in want: cur[want[i]] = int(v, 2) if set(v) <= set("01") else v
print("payload=%s delay=%s" % (hex(cur["payload"]) if isinstance(cur.get("payload"), int) else cur.get("payload"), cur.get("delay")))
