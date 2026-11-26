#!/usr/bin/env python3
import hashlib, json, re, sys, zipfile
from pathlib import Path, PurePosixPath

def verify(z):
    bodies = {}
    for i in z.infolist():
        p = PurePosixPath(i.filename)
        if (p.is_absolute() or ".." in p.parts or str(p) != i.filename or
            i.filename in bodies or i.is_dir() or i.file_size > 1_000_000):
            raise ValueError(f"unsafe or duplicate entry: {i.filename}")
        bodies[i.filename] = z.read(i)
    digest = lambda b: hashlib.sha256(b).hexdigest()
    manifest = dict(tuple(l.split()[::-1]) for l in bodies["ROUND3-SHA256SUMS"].decode().splitlines())
    assert len(manifest) == len(bodies["ROUND3-SHA256SUMS"].splitlines())
    assert manifest.keys() == bodies.keys() - {"ROUND3-SHA256SUMS"}
    for k, v in manifest.items():
        assert digest(bodies[k]) == v, k
    r = json.loads(bodies["round3-receipt.json"])
    for k, v in r["sha256"].items():
        assert digest(bodies[k]) == v, k
    for pin, module in map(str.split, bodies["pinned-git-blobs.tsv"].decode().splitlines()):
        b = bodies[f"SamuelAlexanderResearch/{module}.lean"]
        assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest() == pin, module
    assert r["one_spare"]["whole_status"] == "hand_proof"
    assert r["binary_two_lift"]["whole_status"] == "hand_proof"
    assert r["binary_two_lift"]["fixed_source_color_transfer"] is False
    assert r["observation"]["status"] == "kernel_checked_conditional"
    assert r["observation"]["solver_integration"] is False
    log = bodies["ROUND3-REPLAY.log"].decode()
    assert r["lean"] in log
    assert not re.search(r"sorryAx|error:|warning:",log)
    decls = (r["one_spare"]["lean_components"] + r["binary_two_lift"]["lean_components"] +
             [r["observation"]["lean_endpoint"]] + r["observation"]["controls"])
    for d in decls:
        assert re.search(re.escape(f"'{d}'") + r" (?:depends on axioms:|does not depend on any axioms)", log), d
    print(f"PASS {len(bodies)} archive entries / {len(manifest)} manifest hashes / {len(r['sha256'])} receipt hashes / 9 Git object pins / {len(decls)} scoped declaration lines")

with zipfile.ZipFile(Path(sys.argv[1])) as z:
    verify(z)
