"""Replay exact integer linear combinations with Python and pinned Lean."""
import argparse, hashlib, json, re, subprocess, sys, tempfile, time
from pathlib import Path

PIN = "leanprover/lean4:v4.33.1"
COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
SCHEMA = "commons.linear-int.v1"
LEAN = ["elan", "run", PIN, "lean"]

def require(p, message):
    if not p:
        raise ValueError(message)

def object_pairs(pairs):
    result = {}
    for k, v in pairs:
        require(k not in result, "duplicate JSON key")
        result[k] = v
    return result

def fields(o, keys):
    require(type(o) is dict and set(o) == set(keys), "unexpected object fields")

def bounded(i):
    return type(i) is int and abs(i) <= 10**6

def parse(raw):
    require(len(raw) <= 16384, "certificate too big")
    c = json.loads(raw, object_pairs_hook=object_pairs)
    fields(c, ["schema", "variables", "premises", "target", "multipliers"])
    require(c["schema"] == SCHEMA, "unknown schema")
    vs = c["variables"]
    require(type(vs) is list and 1 <= len(vs) <= 8 and
            all(type(v) is str and re.fullmatch("[A-Za-z][A-Za-z0-9_]{0,31}", v) for v in vs)
            and len(set(vs)) == len(vs), "invalid variable names")
    ps, t, ms = c["premises"], c["target"], c["multipliers"]
    require(type(ps) is list and 1 <= len(ps) <= 12, "invalid premises")
    for row in [*ps,t]:
        fields(row, ["coeffs", "le"])
        co = row["coeffs"]
        require(type(co) is list and len(co)==len(vs) and all(map(bounded, co))
                and bounded(row["le"]), "invalid inequality")
    require(type(ms) is list and len(ms)==len(ps) and
            all(bounded(m) and m >= 0 for m in ms) and any(ms), "invalid multipliers")
    return c

def exact(c):
    ps, t, ms = c["premises"], c["target"], c["multipliers"]
    lhs = [sum(r["coeffs"][i]*m for r,m in zip(ps,ms))
           for i in range(len(c["variables"]))]
    rhs = sum(r["le"]*m for r,m in zip(ps,ms))
    require(lhs == t["coeffs"] and rhs <= t["le"], "invalid linear combination")
    return rhs

def lint(n):
    return "(" + str(n) + " : Int)"

def sint(n):
    return str(n) if n >= 0 else "(- " + str(-n) + ")"

def lean_source(c):
    vs = ["x"+str(i) for i in range(len(c["variables"]))]
    def lhs(r):
        return " + ".join(lint(a)+" * "+x for a,x in zip(r["coeffs"],vs))
    def row(r):
        return lhs(r)+" <= "+lint(r["le"])
    ps = c["premises"]
    args = " ".join("(h"+str(i)+" : "+row(p)+")" for i,p in enumerate(ps))
    derivation = ""
    term = "Int.le_refl 0"
    slack_terms = []
    for i,(p,m) in enumerate(zip(ps,c["multipliers"])):
        slack = lint(p["le"])+" - ("+lhs(p)+")"
        slack_terms.append("("+lint(m)+" * ("+slack+"))")
        derivation += f"  have s{i} : 0 <= {slack} := by omega\n"
    for i in reversed(range(len(ps))):
        term = f"addScaled {c['multipliers'][i]} s{i} ({term})"
    return ("import Lean\nset_option warningAsError true\nset_option maxHeartbeats 1000000\n"
            "theorem addScaled (k : Nat) {v s : Int} (hv : 0 <= v) (hs : 0 <= s) :\n"
            "    0 <= (k : Int) * v + s := Int.add_nonneg (Int.mul_nonneg (by omega) hv) hs\n"
            + "theorem certificate (" + " ".join(vs) + " : Int) " + args + " : "
            + row(c["target"]) + " := by\n" + derivation
            + "  have combined : 0 <= " + "".join("("+s+" + " for s in slack_terms)
            + "0" + ")"*len(ps) + " := " + term + "\n  clear "
            + " ".join(f"h{i} s{i}" for i in range(len(ps)))
            + "\n  omega\n#print axioms certificate\n")

def smt_source(c):
    vs = ["x"+str(i) for i in range(len(c["variables"]))]
    def row(r):
        terms = ["(* "+sint(a)+" "+x+")" for a,x in zip(r["coeffs"],vs)]
        lhs = terms[0] if len(terms)==1 else "(+ "+" ".join(terms)+")"
        return "(<= "+lhs+" "+sint(r["le"])+")"
    lines = ["(set-logic QF_LIA)", *["(declare-const "+x+" Int)" for x in vs],
             *["(assert "+row(p)+")" for p in c["premises"]],
             "(assert (not "+row(c["target"])+"))", "(check-sat)"]
    return "\n".join(lines)+"\n"

def hand_source(c):
    def row(r):
        terms = [f"({a})*{v}" for a,v in zip(r["coeffs"],c["variables"]) if a]
        return (" + ".join(terms) or "0") + f" <= {r['le']}"
    ps, ms, t = c["premises"], c["multipliers"], c["target"]
    bound = exact(c)
    lines = ["Exact integer linear implication (conditional)", "",
             *[f"H{i}: {row(r)}" for i,r in enumerate(ps,1)], "",
             "Multiply each premise by its indicated nonnegative integer and add:",
             " + ".join(f"{m}*H{i}" for i,m in enumerate(ms,1) if m),
             f"The combined left side is the target's left side; the combined bound is {bound}.",
             f"Since {bound} <= {t['le']}, conclude: {row(t)}."]
    return "\n".join(lines)+"\n"

def sha(b):
    return hashlib.sha256(b).hexdigest()

def checked(raw, run_smt=False, timeout=30):
    c = parse(raw)
    bound = exact(c)
    source = lean_source(c).encode()
    version = subprocess.check_output(LEAN+["--version"], text=True, timeout=timeout).strip()
    require(COMMIT in version, "wrong Lean toolchain commit")
    smt = "not-run"
    if run_smt:
        p = subprocess.run(["z3","-in","-smt2"], input=smt_source(c), text=True,
                           capture_output=True, timeout=timeout)
        require(p.returncode == 0 and p.stdout.strip()=="unsat",
                "SMT solver did not return unsat")
        smt = "unsat-advisory"
    with tempfile.TemporaryDirectory(prefix="commons_linear_") as d:
        Path(d, "Replay.lean").write_bytes(source)
        p = subprocess.run(LEAN+["Replay.lean"], cwd=d, text=True,
                           capture_output=True, timeout=timeout)
    require(p.returncode==0, "Lean refused: "+(p.stdout+p.stderr)[:2000])
    line, = p.stdout.strip().splitlines()
    prefix = "'certificate' depends on axioms: ["
    if line == "'certificate' does not depend on any axioms":
        ax = []
    else:
        require(line.startswith(prefix) and line.endswith("]"), "unexpected axiom report")
        ax = line[len(prefix):-1].split(", ")
        require(set(ax) <= {"propext","Quot.sound","Classical.choice"},"nonstandard axioms")
    return {"status":"kernel-checked-conditional","certificate_sha256":sha(raw),
            "checker_sha256":sha(Path(__file__).read_bytes()),"lean_module_sha256":sha(source),
            "lean":version,"axioms":ax,"smt":smt,"exact_combination_bound":bound,
            "variables":c["variables"],"premises":c["premises"],"conclusion":c["target"]}

def batch(directory, budget, maximum, after):
    deadline = time.monotonic()+budget
    files = sorted(f for f in directory.glob("*.json") if f.name > after)
    failed = False
    for i, f in enumerate(files):
        left = deadline-time.monotonic()
        if i >= maximum or left < 1:
            item = {"status":"deferred"}
        else:
            try:
                require(f.is_file() and not f.is_symlink(), "not a regular input")
                with f.open("rb") as stream:
                    item = checked(stream.read(16385), timeout=min(30,left/3))
            except (OSError, ValueError, subprocess.SubprocessError) as exc:
                failed = True
                item = {"status":"not-verified","diagnostic":str(exc)[:2000]}
        item["file"]=f.name
        print(json.dumps(item),flush=True)
    return int(failed)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("action", choices=["check", "render-lean", "render-smt", "render-hand", "batch"])
    p.add_argument("path", type=Path)
    p.add_argument("--smt", action="store_true", help="optional advisory z3 check (check only)")
    p.add_argument("--budget", type=int, default=120)
    p.add_argument("--limit", type=int, default=32)
    p.add_argument("--after", default="", help="resume after the last attempted filename")
    a = p.parse_args()
    if a.action=="batch":
        require(a.path.is_dir() and 1<=a.budget<=14400 and 1<=a.limit<=10000, "invalid batch options")
        return batch(a.path,a.budget,a.limit,a.after)
    with a.path.open("rb") as stream:
        raw=stream.read(16385)
    if a.action=="check":
        print(json.dumps(checked(raw,a.smt),indent=2))
    else:
        c=parse(raw)
        exact(c)
        sys.stdout.buffer.write({"render-lean": lean_source, "render-smt": smt_source, "render-hand": hand_source}[a.action](c).encode("utf-8"))
    return 0

if __name__=="__main__":
    try:
        sys.exit(main())
    except (OSError,ValueError,subprocess.SubprocessError) as exc:
        sys.exit(str(exc))
