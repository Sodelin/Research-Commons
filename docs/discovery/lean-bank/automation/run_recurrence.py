"""Replay one independently pinned Git/Lean recurrence job. No dynamic commands."""
import argparse
import hashlib
import json
import os
import re
import resource
import subprocess
import sys
import tempfile
import time
from pathlib import Path

LIMIT=1 << 20
MAX_LOG=262144
GIT="/usr/bin/git"
DECLARATION="AlexanderZeroRun.arbitrarily_late_run_iff"
SIGNATURE = """example (A : Nat → Prop) (m : Nat) :
    (∀ bound, ∃ s, bound ≤ s ∧ AlexanderZeroRun.IsRun A s (m+1)) ↔ A m :=
  AlexanderZeroRun.arbitrarily_late_run_iff A m
"""
STDLIB_AXIOMS={"propext", "Classical.choice", "Quot.sound"}
HEX=re.compile(r"[0-9a-f]{64}")
COMMIT=re.compile(r"[0-9a-f]{40}")
BASENAME=re.compile(r"[A-Z][A-Za-z0-9_]{0,90}\.lean", re.ASCII)
GITPATH=re.compile(r"[A-Za-z0-9][A-Za-z0-9_./-]{0,200}", re.ASCII)

class Rejected(ValueError):
    pass

def require(b, why):
    if not b:
        raise Rejected(why)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def git_id(data):
    return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()

def match(pat, v):
    return type(v) is str and pat.fullmatch(v) is not None

def pairs(entries):
    out={}
    for name, value in entries:
        require(name not in out, "duplicate JSON key")
        out[name]=value
    return out

def keys(v,*fields):
    require(type(v) is dict and set(v)==set(fields), "unsupported contract fields")

def read_capped(p, max_bytes):
    with p.open("rb") as f:
        data=f.read(max_bytes+1)
    require(len(data) <= max_bytes, "bounded file limit exceeded")
    return data

def load_contract(path, pin):
    raw=read_capped(path, 16384)
    require(match(HEX,pin) and sha(raw)==pin, "contract hash mismatch")
    c=json.loads(raw, object_pairs_hook=pairs)
    keys(c,"schema","job","commit","lean_commit","lean_binary_sha256","sources","declaration","statement_sha256")
    require(c["schema"]=="commons.proofbridge.recurrence-run.v1" and
            c["job"]=="bounded-recurrence-pilot", "unregistered job")
    for k in ("commit","lean_commit"):
        require(match(COMMIT,c[k]), "full commit pin necessary")
    require(match(HEX,c["lean_binary_sha256"]), "invalid Lean binary pin")
    require(c["declaration"]==DECLARATION, "unregistered theorem name")
    require(match(HEX,c["statement_sha256"]), "invalid exact statement pin")
    require(type(c["sources"]) is list and 1 <= len(c["sources"]) <= 6, "source list limit")
    seen=set()
    for s in c["sources"]:
        keys(s,"path","module_file","sha256","git_blob")
        require(match(GITPATH,s["path"]) and all(p not in ("",".","..") for p in s["path"].split("/")),
                "unapproved Git path")
        require(match(BASENAME,s["module_file"]) and s["module_file"] not in {"WorkerAxiomCheck.lean","WorkerExactType.lean"}
                and s["module_file"] not in seen and match(HEX,s["sha256"])
                and match(COMMIT,s["git_blob"]),
                "invalid or duplicate source")
        seen.add(s["module_file"])
    return c

def limits():
    resource.setrlimit(resource.RLIMIT_FSIZE,(64 << 20,64 << 20))
    resource.setrlimit(resource.RLIMIT_CPU,(45,46))
    resource.setrlimit(resource.RLIMIT_AS,(8 << 30,8 << 30))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))

def run(argv, work, timeout, cap, env):
    with tempfile.TemporaryFile(dir=work) as log:
        p=subprocess.run(argv,cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT,
                         stdin=subprocess.DEVNULL,timeout=timeout,check=False,preexec_fn=limits)
        log.seek(0)
        out=log.read(cap+1)
    require(p.returncode==0, f"{Path(argv[0]).name} exited {p.returncode}: "+
            out[:1200].decode(errors="replace"))
    require(len(out)<=cap, "oversized worker output")
    return out

def check(repo, blob_dir, lean, contract, anchor):
    started=time.monotonic()
    require(lean.is_file() and sha(read_capped(lean,16<<20)) == contract["lean_binary_sha256"],
            "Lean binary SHA-256 mismatch")
    with tempfile.TemporaryDirectory(prefix="proofbridge-recurrence-") as raw:
        work=Path(raw)
        env={"PATH":"/usr/bin:/bin","HOME":raw,"LANG":"C.UTF-8","LC_ALL":"C.UTF-8",
             "GIT_CONFIG_NOSYSTEM":"1","GIT_CONFIG_GLOBAL":"/dev/null",
             "GIT_CONFIG_SYSTEM":"/dev/null","GIT_NO_LAZY_FETCH":"1",
             "GIT_NO_REPLACE_OBJECTS":"1","GIT_TERMINAL_PROMPT":"0","LEAN_PATH":raw}
        commit=contract["commit"]
        if repo is not None:
            git=[GIT,"-C",str(repo),"--no-replace-objects"]
            require(run(git+["cat-file","-t",commit],work,4,100,env)==b"commit\n","pin is not a commit")
        version=run([str(lean),"--version"],work,4,512,env).decode()
        require(f"commit {contract['lean_commit']}" in version, "Lean version commit mismatch")
        checks=[]
        staged=[]
        for s in contract["sources"]:
            blob=s["git_blob"]
            if repo is not None:
                actual=run(git+["rev-parse","--verify",f"{commit}:{s['path']}"],work,4,100,env)
                require(actual.decode().strip()==blob,"Git commit path/blob mismatch")
                require(run(git+["cat-file","-t",blob],work,4,100,env)==b"blob\n","expected Git blob")
                source=run(git+["cat-file","blob",blob],work,4,LIMIT,env)
            else:
                source=read_capped(blob_dir/blob,LIMIT)
            require(sha(source)==s["sha256"] and git_id(source)==blob, "Git source hash mismatch")
            path=work/s["module_file"]
            path.write_bytes(source)
            staged.append((s,blob,path))
        for s,blob,path in staged:
            out=run([str(lean),"-j","1","-o",str(path.with_suffix(".olean")),str(path)],work,45,MAX_LOG,env)
            require(not re.search(rb"(?:error:|warning:|sorryAx)",out), "unexpected Lean diagnostic")
            checks.append({"source_path":s["path"],"git_blob":blob,"sha256":s["sha256"],
                           "module_file":s["module_file"],"diagnostic_sha256":sha(out)})
        decl=contract["declaration"]
        imports="".join(f"import {Path(s['module_file']).stem}\n" for s in contract["sources"])
        type_probe=work/"WorkerExactType.lean"
        type_probe.write_text(imports+f"set_option pp.fullNames true\n#check {decl}\n",encoding="utf-8")
        exact_type=run([str(lean),"-j","1",str(type_probe)],work,25,MAX_LOG,env)
        require(sha(exact_type)==contract["statement_sha256"], "Lean exact statement SHA-256 mismatch")
        wrapper=work/"WorkerAxiomCheck.lean"
        wrapper.write_text(imports+SIGNATURE+f"#print axioms {decl}\n",encoding="utf-8")
        out=run([str(lean),"-j","1",str(wrapper)],work,25,MAX_LOG,env).decode()
        m=re.fullmatch(r"'"+re.escape(decl)+r"' depends on axioms: \[([^\]]*)\]\s*",out)
        empty=out.strip()==f"'{decl}' does not depend on any axioms"
        require(m is not None or empty,"unrecognized or ambiguous axiom output")
        axioms=[] if empty else [a.strip() for a in m.group(1).split(",")]
        require(set(axioms)<=STDLIB_AXIOMS and len(set(axioms))==len(axioms),"non-whitelisted axiom")
        return {"schema":"commons.proofbridge.recurrence-receipt.v1","job":contract["job"],
                "contract_sha256":anchor,"source_commit":commit,"sources":checks,
                "commit_binding":"local_git_tree_checked" if repo is not None else "independent_contract_tree_binding",
                "lean_version":version.strip(),"lean_binary_sha256":contract["lean_binary_sha256"],
                "declaration":decl,"statement":exact_type.decode().strip(),
                "statement_sha256":contract["statement_sha256"],"signature_sha256":sha(SIGNATURE.encode()),
                "axioms":axioms,"axiom_output":out.strip(),
                "worker_sha256":sha(Path(__file__).read_bytes()),
                "fresh_checker_execution":True,"disposition":"kernel_checked_at_contract_scope",
                "wall_seconds":round(time.monotonic()-started,6)}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    paths=p.add_mutually_exclusive_group(required=True)
    paths.add_argument("--repo")
    paths.add_argument("--blob-dir")
    for flag in ("lean","contract","contract-sha256"):
        p.add_argument("--"+flag,required=True)
    a=p.parse_args()
    try:
        c=load_contract(Path(a.contract),a.contract_sha256)
        v=check(Path(a.repo).resolve(strict=True) if a.repo else None,
                Path(a.blob_dir).resolve(strict=True) if a.blob_dir else None,
                Path(a.lean).resolve(strict=True),c,a.contract_sha256)
    except (ValueError,OSError,RecursionError,subprocess.TimeoutExpired) as ex:
        print(json.dumps({"disposition":"rejected","reason":str(ex)}))
        return 2
    print(json.dumps(v,indent=2))
    return 0

if __name__=="__main__":
    sys.exit(main())
