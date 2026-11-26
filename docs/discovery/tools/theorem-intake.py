"""Agent-readable theorem intake over source-pinned Commons catalogs."""
import argparse, hashlib, json, re, subprocess, sys
from collections import Counter
from pathlib import Path, PurePosixPath

HEX = re.compile(r"[0-9a-f]{40}")
KINDS = {"claim_board","obligations","hand_sections","incorporation","handoff","certificate_records","recovered_claims","recovered_files","preservation","binding_inventory","package_claims","exact_lean_bindings","reading_guide"}
FIELDS = {"schema","sources"}
CERT_SCHEMA = "commons.linear-int.v1"
ROUND_SCHEMA = "commons.proofbridge.rounded_batch_input.v1"
ROUND_RESULT = "commons.proofbridge.rounded_discovery_result.v1"
DEFAULT_RESULT = "commons.proofbridge.discovery_result.v1"
CHECKER_SHA = "8872348bfde6b6961e985e8bcfac1db320239e973b84cb79d3b36ec065ae7ee5"

def wire(o):
    return (json.dumps(o,sort_keys=True,ensure_ascii=True)+"\n").encode("ascii")

def hex256(s):
    return type(s) is str and re.fullmatch(r"[0-9a-f]{64}",s) is not None

def safe_axioms(a):
    return type(a) is list and all(type(x) is str and
                x in {"propext","Quot.sound","Classical.choice"} for x in a)


def need(ok,msg):
    if not ok:
        raise ValueError(msg)

def strict(pairs):
    o={}
    for k,v in pairs:
        need(k not in o,"duplicate JSON key")
        o[k]=v
    return o

def decode(b):
    return json.loads(b,object_pairs_hook=strict)

def git(repo,*args):
    p=subprocess.run(["git","-C",str(repo),*args],capture_output=True,timeout=20)
    need(p.returncode==0,"pinned Git object unavailable: "+p.stderr.decode(errors="replace")[:300])
    return p.stdout

def source(repo,pin):
    need(type(pin) is dict and set(pin)=={"kind","commit","path","blob"},"invalid pin")
    need(pin["kind"] in KINDS and type(pin["commit"]) is str and HEX.fullmatch(pin["commit"])
         and type(pin["blob"]) is str and HEX.fullmatch(pin["blob"]),"invalid source hashes or kind")
    path=pin["path"]
    need(type(path) is str and re.fullmatch(r"[A-Za-z0-9_./-]+",path)
         and not PurePosixPath(path).is_absolute() and all(p not in {"",".",".."} for p in path.split("/")),
         "invalid source path")
    obj=pin["commit"]+":"+path
    need(git(repo,"rev-parse","--verify",obj).decode().strip()==pin["blob"],
         "pinned Git blob mismatch: "+path)
    need(int(git(repo,"cat-file","-s",pin["blob"]))<=8*1024*1024,"oversized catalog")
    raw=git(repo,"cat-file","blob",pin["blob"])
    return raw, {**pin,"sha256":hashlib.sha256(raw).hexdigest()}

def project(kind,raw,provenance):
    def row(i, category, statement, math=None, formal=None, evidence=None, relation=None,
            queue="needs_statement_review", certificate=None):
        need(type(i) is str and i,"missing stable record ID")
        return {"id":kind+":"+i,"original_id":i,"record_kind":category,
                "statement":statement,"authored_math_status":math,
                "authored_formal_status":formal,"evidence":evidence or [],
                "related_ids":relation or [],"intake_status":queue,
                "certificate":certificate,"provenance":provenance}
    if kind=="hand_sections":
        lines=raw.decode("utf-8").splitlines()
        starts=[i for i,l in enumerate(lines) if l.startswith("## ")]
        for n,i in enumerate(starts):
            title=lines[i][3:].strip()
            end=starts[n+1] if n+1<len(starts) else len(lines)
            loc={**provenance,"start_line":i+1,"end_line":end}
            id_slug=re.sub(r"[^a-z0-9]+","-",title.lower()).strip("-")
            entry=row(provenance["path"]+"#"+id_slug,"proof_note_section",title)
            entry["provenance"]=loc
            yield entry
        return
    o=decode(raw)
    if kind=="claim_board":
        for c in o["claims"]:
            completion=c.get("completion",{})
            yield row(c["canonical_key"],c["claim_kind"],c.get("exact_statement_and_scope"),
                      c.get("mathematical_status"),completion.get("formal_verification"),
                      c.get("accepted_artifacts"),c.get("dependencies"))
    elif kind=="obligations":
        for c in o["obligations"]:
            yield row(c["id"],"research_obligation",c.get("original_obligation"),c.get("status"),
                      None,c.get("providers"),c.get("cross_goal_dependencies"))
    elif kind=="incorporation":
        for c in o["entries"]:
            r=c["register_record"]
            yield row(c["id"],"incorporation_record",r.get("original_obligation"),
                      r.get("status"),c.get("current_incorporation"),
                      c.get("counterpart_checks"),["obligations:"+c["id"]])
    elif kind=="recovered_claims":
        for c in o["entries"]:
            yield row(c["key"],"recovered_scoped_claim",c["scope"],c["mathematical_status"],
                      c["formal_status"],[{k:c[k] for k in
                      ("file","companions","gap","independent_review","proof_authorship")}],
                      queue="needs_statement_review")
    elif kind=="recovered_files":
        for c in o["files"]:
            yield row(c["name"],"recovered_source_file",c["title"],None,None,
                      [{k:c[k] for k in ("kind","public_sha256","public_git_blob_sha",
                                         "new_independent_review","new_lean_execution")}],
                      queue="source_only")
    elif kind=="preservation":
        for c in o["components"]:
            yield row(c["public_root"],"preserved_packet",None,None,None,[c],
                      queue="source_only")
    elif kind=="binding_inventory":
        for c in o["claims"]:
            yield row(c["claim_id"],"historical_binding_inventory",c["exact_canonical_scope"],
                      c["canonical_mathematical_status_unchanged"],
                      c["canonical_completion_unchanged"].get("formal_verification"),
                      [{"candidate_qualified_reuse":c["candidate_qualified_reuse"],
                        "historical_package_lean_module":c["package_lean_module"],
                        "missing_interface_or_join":c["missing_exact_interface_or_join"],
                        "binding_adopted":c["binding_adopted"],"source_evidence":c["source_evidence"]}],
                      queue="reuse_audit_not_a_batch_job")
    elif kind=="package_claims":
        for c in o["claims"]:
            yield row(c["claim_id"],"package_binding_record",None,None,c["lean"].get("state"),
                      [{"lean":c["lean"],"rust":c["rust"],"verification":c["verification"],
                        "source_artifacts":c["source_artifacts"]}],c.get("dependencies"),
                      queue="reuse_audit_not_a_batch_job")
    elif kind=="exact_lean_bindings":
        for c in o["bindings"]:
            yield row(c["claim"],"named_lean_binding",c["conclusion"],None,None,[c],
                      queue="reuse_audit_not_a_batch_job")
    elif kind=="reading_guide":
        tracked={q["path"]:q for q in o["sources"]}
        for c in o["navigation"]:
            q=tracked[c["source_path"]]
            need(type(c["start_line"]) is int and type(c["end_line"]) is int and
                 1<=c["start_line"]<=c["end_line"],"invalid reading span")
            loc={**provenance,
                 "declared_source_path":str(PurePosixPath(provenance["path"]).parent / q["path"]),
                 "declared_source_sha256":q["sha256"],"start_line":c["start_line"],
                 "end_line":c["end_line"],"scope":"guide_metadata_only"}
            entry=row(c["id"],"editorial_proof_locator",c["title"],None,None,
                      [{"evidence_scope":c["evidence_scope"],"source_evidence":q.get("evidence")}],
                      c.get("related_claims"))
            entry["provenance"]=loc
            yield entry
    elif kind=="handoff":
        need(o["schema"]=="commons.proofbridge.handoff.v1","unknown handoff")
        verified=o["verification"]
        yield row(o["theorem_id"],"conditional_theorem",
                  {"premises":verified["premises"],"conclusion":verified["conclusion"]},
                  "conditional_on_supplied_premises",verified["status"],[o],None,
                  "recorded_kernel_handoff",o["source"])
    elif kind=="certificate_records":
        need(o["schema"]=="commons.proofbridge.certificate_records.v1","unknown record list")
        for c in o["records"]:
            typed=c["certificate"]
            need(type(typed) is dict,"unsupported record schema")
            core=typed
            if typed.get("schema")==ROUND_SCHEMA:
                need(set(typed)=={"schema","scale","certificate"}
                     and type(typed["scale"]) is int and 1<=typed["scale"]<=1000,
                     "invalid rounded envelope")
                core=typed["certificate"]
            need(type(core) is dict and core.get("schema")==CERT_SCHEMA,"unsupported record schema")
            yield row(c["id"],"proposed_conditional_theorem",
                      {"premises":core["premises"],"conclusion":core["target"]},
                      None,None,[],c.get("related_ids"),"ready_for_checker",typed)

def queue_revision(repo,ref):
    need(type(ref) is str and re.fullmatch(r"[A-Za-z0-9_./-]+",ref)
         and not ref.startswith("-"),"invalid queue revision")
    commit=git(repo,"rev-parse","--verify",ref+"^{commit}").decode().strip()
    need(HEX.fullmatch(commit),"invalid queue commit")
    return commit

def tracked_records(repo, ref):
    commit=queue_revision(repo,ref)
    root="research/proofbridge-incoming"
    paths=git(repo,"ls-tree","-r","--name-only",commit,"--",root).decode().splitlines()
    need(len(paths)<=512,"too many queue files for one pass")
    for p in paths:
        if re.fullmatch(root+r"/[A-Za-z0-9_-]+\.json",p):
            blob=git(repo,"rev-parse","--verify",commit+":"+p).decode().strip()
            yield {"commit":commit,"path":p,"blob":blob,"kind":"certificate_records"}

def queue_rows(repo, ref):
    rows={}
    for pin in tracked_records(repo,ref):
        raw,provenance=source(repo,pin)
        for row in project(pin["kind"],raw,provenance):
            need(len(rows)<2048,"too many staged records for a delta pass")
            need(row["id"] not in rows,"duplicate stable ID: "+row["id"])
            rows[row["id"]]=row
    return rows

def queue_delta(repo, before, at):
    base, head=queue_revision(repo,before),queue_revision(repo,at)
    p=subprocess.run(["git","-C",str(repo),"merge-base","--is-ancestor",base,head],
                     capture_output=True,timeout=20)
    need(p.returncode==0,"queue delta base is not an available ancestor")
    old,new=queue_rows(repo,base),queue_rows(repo,head)
    def key(row):
        return row["provenance"]["path"],hashlib.sha256(wire(row["certificate"])).hexdigest()
    added=sorted(set(new)-set(old))
    removed=sorted(set(old)-set(new))
    changed=sorted(i for i in set(new)&set(old) if key(new[i])!=key(old[i]))
    need(len(added)+len(changed)<=512,"delta exceeds one bounded batch")
    sameness=len(new)-len(added)-len(changed)
    return ([new[i] for i in sorted(added+changed)],
            {"schema":"commons.proofbridge.queue_delta.v1","base_commit":base,"head_commit":head,
             "added":added,"changed":changed,"removed":removed,"unchanged_count":sameness,
             "unchanged_evidence_status":"not_replayed_this_delta"})


def intake(repo, manifest, queue_ref=None):
    o=decode(manifest.read_bytes())
    need(set(o)==FIELDS and o["schema"]=="commons.theorem_sources.v1"
         and type(o["sources"]) is list and 0<len(o["sources"])<=100,"invalid source manifest")
    records={}
    pins=[*o["sources"], *(tracked_records(repo,queue_ref) if queue_ref else [])]
    for p in pins:
        raw, provenance=source(repo,p)
        for r in project(p["kind"],raw,provenance):
            need(r["id"] not in records,"duplicate stable ID: "+r["id"])
            records[r["id"]]=r
    return records

def emit(o):
    sys.stdout.buffer.write((json.dumps(o,sort_keys=True,ensure_ascii=True)+"\n").encode("ascii"))

def export_ready(rows, out, delta=None):
    selected=[r for r in rows if r["intake_status"]=="ready_for_checker"]
    out.mkdir(exist_ok=False)
    inputs=out/"inputs"
    inputs.mkdir()
    jobs=[]
    for r in selected:
        ident=r["id"]
        name=hashlib.sha256(ident.encode()).hexdigest()+".json"
        raw=wire(r["certificate"])
        (inputs/name).write_bytes(raw)
        jobs.append({"id":ident,"file":name,"sha256":hashlib.sha256(raw).hexdigest(),
                     "provenance":r["provenance"]})
    index={"schema":"commons.theorem_intake.checker_export.v1","jobs":jobs,
           "not_exported_count":len(rows)-len(jobs)}
    if delta is not None:
        index["queue_delta"]=delta
    (out/"index.json").write_bytes((json.dumps(index,indent=2,ensure_ascii=True)+"\n").encode("ascii"))
    emit(index)

def join_results(records, index_path, results_path):
    index=decode(index_path.read_bytes())
    need(index["schema"]=="commons.theorem_intake.checker_export.v1","wrong export schema")
    jobs={j["file"]:j for j in index["jobs"]}
    seen=set()
    with results_path.open("rb") as stream:
        for line in stream:
            need(len(line)<=65536,"oversized result row")
            q=decode(line)
            n=q.get("file")
            need(n in jobs and n not in seen,"unexpected or duplicate checker result")
            seen.add(n)
            j=jobs[n]
            r=records[j["id"]]
            canonical=wire(r["certificate"])
            need(r["intake_status"]=="ready_for_checker" and r["provenance"]==j["provenance"]
                 and hashlib.sha256(canonical).hexdigest()==j["sha256"],"stale export")
            wrapped=r["certificate"]
            is_round=wrapped["schema"]==ROUND_SCHEMA
            need(q.get("schema")==(ROUND_RESULT if is_round else DEFAULT_RESULT),
                 "wrong checker result schema; regenerate the Discovery projection")
            need(q.get("certificate_sha256")==j["sha256"] and
                 q.get("checker_sha256")==CHECKER_SHA,
                 "checker result certificate or checker hash mismatch")
            status=q.get("status")
            need(status in {"kernel-checked-conditional","not-verified","deferred"},"unknown check result")
            if status=="kernel-checked-conditional" and is_round:
                check_round(wrapped,q)
            elif status=="kernel-checked-conditional":
                axioms=q.get("axioms")
                need(type(q.get("lean")) is str and
                     "commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6," in q["lean"]
                     and type(axioms) is list and all(type(x) is str and
                         x in {"propext","Quot.sound","Classical.choice"} for x in axioms)
                     and type(q.get("lean_module_sha256")) is str
                     and re.fullmatch(r"[0-9a-f]{64}",q["lean_module_sha256"])
                     and q.get("variables")==r["certificate"]["variables"]
                     and q.get("premises")==r["statement"]["premises"]
                     and q.get("conclusion")==r["statement"]["conclusion"],
                     "checker result scope or hash mismatch")
            r["imported_replay"]={"evidence_status":"provided_receipt_not_recompiled",
                                  "result":q}
            # Authored mathematical and formal status are intentionally untouched.

def check_round(wrapped,q):
    cert=wrapped["certificate"]
    scale=wrapped["scale"]
    target=cert["target"]
    intermediate={"coeffs":[scale*x for x in target["coeffs"]],
                  "le":scale*(target["le"]+1)-1}
    def inner(o):
        return (json.dumps(o,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")
    mid=hashlib.sha256(inner({**cert,"target":intermediate})).hexdigest()
    name="PB_"+mid
    files=q.get("files_sha256")
    helpers=q.get("rounded_helper_sha256")
    need(type(files) is dict and set(files)=={name+".lean",name+".olean","ReuseOriginal.lean"}
         and all(hex256(x) for x in files.values())
         and type(helpers) is dict and set(helpers)=={"assumption_relay.py","import_reduced.py",
                                                    "premise_handoff.py","rounded_witness.py"}
         and all(hex256(x) for x in helpers.values()),"rounded artifact or helper pins missing")
    need(q.get("source_sha256")==hashlib.sha256(inner(cert)).hexdigest()
         and q.get("intermediate_certificate_sha256")==mid
         and type(q.get("lean")) is str
         and "commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6," in q["lean"]
         and safe_axioms(q.get("provider_axioms")) and safe_axioms(q.get("consumer_axioms"))
         and wire({k:q.get(k) for k in ("variables","premises","multipliers","target","scale","intermediate_target")})==
               wire({**{k:cert[k] for k in ("variables","premises","multipliers","target")},
                     "scale":scale,"intermediate_target":intermediate}),
         "rounded checker result scope or hash mismatch")


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    default=Path(__file__).resolve().parents[3]
    ap.add_argument("--repo",type=Path,default=default)
    ap.add_argument("--sources",type=Path,default=Path(__file__).with_name("catalog-sources.json"))
    ap.add_argument("--include-queue-at",metavar="REVISION")
    ap.add_argument("--queue-delta-since",metavar="BASE_REVISION",help="export added and changed typed jobs only")
    ap.add_argument("--status")
    ap.add_argument("--kind")
    ap.add_argument("--math-status")
    ap.add_argument("--formal-status")
    ap.add_argument("--id")
    ap.add_argument("--query",type=str)
    ap.add_argument("--summary",action="store_true")
    ap.add_argument("--emit-certificate",action="store_true")
    ap.add_argument("--export-ready",type=Path)
    ap.add_argument("--checker-results",type=Path)
    ap.add_argument("--export-index",type=Path)
    a=ap.parse_args()
    if a.queue_delta_since is not None:
        need(a.include_queue_at and a.export_ready and not any((
            a.status,a.kind,a.math_status,a.formal_status,a.id,a.query,a.summary,
            a.emit_certificate,a.checker_results,a.export_index)),
            "queue delta requires unfiltered --include-queue-at and --export-ready")
        rows,delta=queue_delta(a.repo,a.queue_delta_since,a.include_queue_at)
        export_ready(rows,a.export_ready,delta)
        return
    rs=intake(a.repo,a.sources,a.include_queue_at)
    need(bool(a.checker_results)==bool(a.export_index),"use both result and export-index paths")
    if a.checker_results:
        join_results(rs,a.export_index,a.checker_results)
    if a.emit_certificate:
        need(a.id in rs,"a known --id is required")
        r=rs[a.id]
        cert=r["certificate"]
        if r["intake_status"]=="recorded_kernel_handoff":
            path=cert["path"]
            need(type(path) is str and re.fullmatch(r"[A-Za-z0-9_./-]+",path)
                 and all(x not in {"",".",".."} for x in path.split("/"))
                 and HEX.fullmatch(cert["commit"]),"invalid certificate source")
            raw=git(a.repo,"show",cert["commit"]+":"+path)
            need(len(raw)<=16384 and hashlib.sha256(raw).hexdigest()==cert["sha256"],
                 "certificate source hash mismatch")
            cert=decode(raw)
            need(cert.get("schema")==CERT_SCHEMA,"unsupported certificate source")
        else:
            need(r["intake_status"]=="ready_for_checker","no checker input is registered for this ID")
        emit(cert)
        return
    rows=[r for r in rs.values() if (not a.id or a.id==r["id"])
          and (not a.status or a.status==r["intake_status"])
          and (not a.kind or a.kind==r["record_kind"])
          and (not a.math_status or a.math_status==r["authored_math_status"])
          and (not a.formal_status or a.formal_status==r["authored_formal_status"])
          and (not a.query or a.query.casefold() in json.dumps(r,ensure_ascii=False).casefold())]
    rows.sort(key=lambda r:r["id"])
    if a.export_ready:
        export_ready(rows,a.export_ready)
    elif a.summary:
        emit({"schema":"commons.theorem_intake.summary.v1","rows":len(rows),
              "intake_status":Counter(r["intake_status"] for r in rows),
              "source_kind":Counter(r["provenance"]["kind"] for r in rows)})
    else:
        for r in rows:
            emit({"schema":"commons.theorem_intake.record.v1",**r})

if __name__=="__main__":
    try:
        main()
    except (OSError,TypeError,ValueError,KeyError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        sys.exit(2)
