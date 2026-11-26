#!/usr/bin/env python3
"""Offline ProofBridge exact-ID catalog and immutable artifact lock exporter."""
import argparse
import hashlib
import json
import re
import sys
from pathlib import PurePosixPath

VERSION = "proofbridge.catalog.v1"
LOCK_VERSION = "proofbridge.artifact-lock.v1"
ID = r"[a-z][a-z0-9_-]*(?:\.[a-z0-9_-]+)+"
COMMIT = r"(?:[0-9a-f]{40}|[0-9a-f]{64})"
SHA256 = r"[0-9a-f]{64}"
REPO = r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+"
STATUS = {"open", "partial", "conditional", "closed"}
RELATION = {"exact", "partial", "conditional", "related"}
EVIDENCE = {"source_only", "remote_ci", "local_replay", "kernel_checked"}
PROOF_STATUS = {"conjectural", "hand_proof", "checked_component", "kernel_checked"}
USES = {"uses", "may_use", "extends"}
SOURCES = {"primary", "internal", "derived", "external"}


def fail(msg):
    raise ValueError(msg)


def schema(obj, fields):
    if type(obj) is not dict or set(obj) != set(fields.split()):
        fail(f"expected fields: {fields}")


def string(obj, label="text"):
    if type(obj) is not str or not obj.strip():
        fail(f"invalid {label}")
    return obj


def match(obj, pattern, label):
    if not re.fullmatch(pattern, string(obj, label)):
        fail(f"invalid {label}: {obj}")
    return obj


def enum(obj, choices, label):
    if string(obj, label) not in choices:
        fail(f"invalid {label}: {obj}")


def records(items):
    if type(items) is not list:
        fail("expected list")
    return items


def digest(statement):
    """Strict UTF-8 content identity, not symbolic statement equivalence."""
    return hashlib.sha256(string(statement).encode()).hexdigest()


def canonical(obj):
    return json.dumps(obj, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def load(path):
    def object_pairs(items):
        obj = dict(items)
        if len(obj) != len(items):
            fail("duplicate JSON key")
        return obj
    with open(path, encoding="utf-8") as stream:
        return json.load(stream, object_pairs_hook=object_pairs)


def check_provenance(obj):
    schema(obj, "kind reference")
    enum(obj["kind"], SOURCES, "provenance kind")
    string(obj["reference"], "provenance reference")


def _indexed(items, kind, index):
    for row in records(items):
        if type(row) is not dict:
            fail("expected row object")
        key = match(row.get("id"), ID, "ID")
        if not key.startswith(kind + "."):
            fail(f"{key}: expected {kind}. ID")
        if key in index:
            fail(f"duplicate ID: {key}")
        index[key] = row
        yield key, row


class Catalog:
    def __init__(self, obj):
        schema(obj, "schema problems theorems artifacts")
        if obj["schema"] != VERSION:
            fail("unsupported catalog")
        self.index = {}
        self.problems = {}
        self.theorems = {}
        self.artifacts = {}
        for key,row in _indexed(obj["problems"], "problem", self.index):
            schema(row, "id title statement closure provenance")
            string(row["title"])
            string(row["statement"])
            enum(row["closure"], STATUS, "closure")
            check_provenance(row["provenance"])
            self.problems[key] = row
        for key,row in _indexed(obj["artifacts"], "artifact", self.index):
            schema(row, "id repo commit path declaration sha256 verification provenance")
            match(row["repo"], REPO, "repository owner/name")
            if any(x in {".", ".."} for x in row["repo"].split("/")):
                fail(f"{key}: noncanonical repository")
            match(row["commit"], COMMIT, "full Git commit")
            path = string(row["path"], "path")
            if path == "." or str(PurePosixPath(path)) != path or path.startswith("/") or \
                "\\" in path or any(x in {".",".."} for x in PurePosixPath(path).parts):
                fail(f"{key}: noncanonical path")
            if row["declaration"] is not None:
                string(row["declaration"], "Lean declaration")
            if row["sha256"] is not None:
                match(row["sha256"], SHA256, "source hash")
            check_provenance(row["provenance"])
            v = row["verification"]
            schema(v, "kind reference lean_version statement_sha256")
            enum(v["kind"], EVIDENCE, "verification")
            if v["kind"] == "source_only":
                if any(v[k] is not None for k in ("reference","lean_version","statement_sha256")):
                    fail(f"{key}: source-only must not carry attestation")
            else:
                string(v["reference"], "verification receipt")
                string(v["lean_version"], "Lean version")
                if v["statement_sha256"] is not None:
                    match(v["statement_sha256"], SHA256, "verified statement hash")
                if v["kind"] == "kernel_checked" and \
                  (row["declaration"] is None or row["sha256"] is None or v["statement_sha256"] is None):
                    fail(f"{key}: kernel claim requires source and statement identity")
            self.artifacts[key] = row
        for key,row in _indexed(obj["theorems"], "theorem", self.index):
            fields = "id title statement assumptions problems artifacts provenance proof_status"
            schema(row, fields + (" uses" if "uses" in row else ""))
            enum(row["proof_status"], PROOF_STATUS, "theorem proof status")
            string(row["title"])
            string(row["statement"])
            for h in records(row["assumptions"]):
                string(h, "assumption")
            check_provenance(row["provenance"])
            seen = set()
            for link in records(row["problems"]):
                schema(link, "id relation")
                p = self.ref(link["id"], self.problems)
                if p["id"] in seen:
                    fail(f"{key}: duplicate problem link")
                seen.add(p["id"])
                enum(link["relation"], RELATION, "problem relation")
                if link["relation"] == "exact" and \
                  (row["statement"] != p["statement"] or row["assumptions"]):
                    fail(f"{key}: exact coverage needs identical statement and no extra assumptions")
            seen = set()
            for a in records(row["artifacts"]):
                resolved = self.ref(a, self.artifacts)
                if a in seen:
                    fail(f"{key}: duplicate artifact link")
                seen.add(a)
                d = resolved["verification"]["statement_sha256"]
                if d is not None and d != digest(row["statement"]):
                    fail(f"{key}: artifact {a} attests a different statement")
            if row["proof_status"] == "kernel_checked" and "kernel_checked" not in self.theorem_evidence(row):
                fail(f"{key}: theorem-level kernel status requires matching artifact evidence")
            self.theorems[key] = row
        for key,t in self.theorems.items():
            seen = set()
            for link in records(t.get("uses", [])):
                schema(link, "id relation")
                self.ref(link["id"], self.theorems)
                enum(link["relation"], USES, "theorem relation")
                if key == link["id"] or link["id"] in seen:
                    fail(f"{key}: self or duplicate theorem link")
                seen.add(link["id"])
        for p in self.problems.values():
            if p["closure"] == "closed" and not any(v["relation"] == "exact"
                for t in self.theorems.values() for v in t["problems"] if v["id"] == p["id"] and t["proof_status"] != "conjectural"):
                fail(f'{p["id"]}: closed requires a linked exact theorem; cannot promote partial work')

    @staticmethod
    def ref(key, table):
        key = match(key, ID, "reference ID")
        if key not in table:
            fail(f"dangling or wrong-kind reference: {key}")
        return table[key]

    def linked_theorems(self, key):
        p = self.ref(key, self.problems)
        return [(t,l["relation"]) for t in sorted(self.theorems.values(), key=lambda t:t["id"])
                for l in t["problems"] if l["id"] == p["id"]]

    def theorem_evidence(self,t):
        # Metadata classification only; no proof backend runs in this tool.
        return sorted({self.artifacts[k]["verification"]["kind"] for k in t["artifacts"]})

    def show(self,key):
        row = self.ref(key, self.index)
        if key in self.problems:
            ts = self.linked_theorems(key)
            return {**row,"linked_theorems":[{"id":t["id"],"relation":r,"proof_status":t["proof_status"],
                                             "evidence":self.theorem_evidence(t)} for t,r in ts],
                    "has_exact_kernel_attestation":any(r=="exact" and
                       "kernel_checked" in self.theorem_evidence(t) for t,r in ts)}
        if key in self.theorems:
            return {**row,"artifact_evidence": self.theorem_evidence(row),
                   "used_by": [{"id": t["id"],"relation": l["relation"]}
                               for t in sorted(self.theorems.values(), key=lambda t: t["id"])
                               for l in t.get("uses",[]) if l["id"] == key]}
        return {**row,"linked_theorem_ids":sorted(t["id"] for t in self.theorems.values() if key in t["artifacts"])}

    def search(self,query):
        tokens=string(query).casefold().split()
        return [{"id":key,"summary":row.get("title",row.get("declaration"))}
                for key,row in sorted(self.index.items())
                if all(tok in canonical(row).casefold() for tok in tokens)]

    def lock(self,key):
        row = self.ref(key, self.index)
        def theorem_lock(seed):
            waiting = list(seed)
            seen = set()
            picked = set()
            while waiting:
                key = waiting.pop()
                if key in seen:
                    continue
                seen.add(key)
                t = self.theorems[key]
                picked.update(t["artifacts"])
                waiting.extend(l["id"] for l in t.get("uses", []) if l["relation"] == "uses")
            return picked

        if key in self.problems:
            artifact_ids=theorem_lock(t["id"] for t,_ in self.linked_theorems(key))
        elif key in self.theorems:
            artifact_ids=theorem_lock([key])
        else:
            artifact_ids={key}
        artifacts = [{k:self.artifacts[a][k] for k in
                    ("id","repo","commit","path","declaration","sha256","verification")}
                    for a in sorted(artifact_ids)]
        return {"schema":LOCK_VERSION,"root_id":key,"artifacts":artifacts}


def main(argv=None):
    parser=argparse.ArgumentParser()
    parser.add_argument("catalog")
    parser.add_argument("operation",choices=("validate","search","show","lock"))
    parser.add_argument("term",nargs="?")
    args=parser.parse_args(argv)
    try:
        c=Catalog(load(args.catalog))
        if args.operation=="validate":
            if args.term is not None:
                fail("validate accepts no argument")
            result={"ok":True,"problems":len(c.problems),"theorems":len(c.theorems),"artifacts":len(c.artifacts)}
        else:
            if args.term is None:
                fail(f"{args.operation} requires an argument")
            result=getattr(c,args.operation)(args.term)
    except (ValueError,OSError,RecursionError) as err:
        print(json.dumps({"ok":False,"error":str(err)}),file=sys.stderr)
        return 2
    print(json.dumps(result,sort_keys=True,indent=2))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
