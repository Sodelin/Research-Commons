"""Link exact Discovery IDs to already-recorded package bindings, not fresh builds."""
import argparse
import collections
import json
from pathlib import Path

# Reviewed aliases only. The source declaration set is not replaced by
# the larger package claim: the G2 source row covers only the timed subset.
ALIASES = {
    "exact_lean_bindings:G1 original-class common core and all-n sharpness":
        ("CB-G1-001","48016978535cefe35b445e3d0b8a4296fbc5849b",
         ["actual_G1_original_class_master_with_all_n_sharpness"],"exact_source_endpoint"),
    "exact_lean_bindings:G2 actual natural/controlled complete timed all-panel projectivity":
        ("CB-G2-001","161f963dfdb12877f0630990a1a1baa93230fbee",
         ["actual_registered_timed_all_panel_projectivity","actual_natural_complete_timed_all_panel_projectivity",
          "actual_controlled_complete_timed_all_panel_projectivity"],"timed_source_subset"),
}


def id_for(row):
    p=row["provenance"]["kind"]
    if p in {"binding_inventory","package_claims"}:
        return row["original_id"],"exact_claim_id"
    if p=="exact_lean_bindings" and row["id"] in ALIASES:
        cid,blob,names,scope=ALIASES[row["id"]]
        src=row["evidence"][0]
        if src["git_blob"]==blob and src["declarations"]==names:
            return cid,scope
    return None,None


def group(records, lookups):
    packages={}
    for row in records:
        if row["provenance"]["kind"]=="package_claims":
            k=row["original_id"]
            if k in packages:
                raise ValueError("duplicate package claim")
            packages[k]=row
    joined={}
    unmatched=[]
    for row in lookups:
        cid,scope=id_for(row)
        if cid not in packages:
            unmatched.append({"id":row["id"],"reason":"no_exact_identity_link"})
            continue
        p=packages[cid]
        evidence=p["evidence"][0]
        lean=evidence["lean"]
        receipts=[x for x in evidence["verification"]
                  if x.get("whole_claim_formal_binding") is True and x.get("record")]
        match=(lean["state"]=="verified_binding" and lean["coverage"]=="exact_canonical_endpoint_exports"
               and lean["declarations"] and receipts)
        status=("recorded_adopted_binding" if match else
                "pending_binding" if lean["state"]=="pending_binding" else
                "insufficient_adoption_evidence")
        if cid not in joined:
            joined[cid]={"claim_id":cid,"status":status,"package_provenance":p["provenance"],
                         "package_module":lean.get("module"),"package_declarations":lean["declarations"],
                         "package_scope":lean.get("scope"),"registered_receipts":receipts,
                         "source_links":[]}
        link={"id":row["id"],"scope":scope,"provenance":row["provenance"]}
        if row["provenance"]["kind"]=="exact_lean_bindings":
            link["declarations"]=row["evidence"][0]["declarations"]
        joined[cid]["source_links"].append(link)
    return {"groups":[joined[k] for k in sorted(joined)],"unmatched":unmatched,
            "counts":dict(collections.Counter(g["status"] for g in joined.values()))}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("catalog",type=Path,help="snapshot from the source-pinned theorem intake")
    p.add_argument("audit",type=Path,help="twenty-record audit receipt")
    a=p.parse_args()
    with a.catalog.open(encoding="utf-8") as f:
        rows=[json.loads(l) for l in f]
    index={r["id"]:r for r in rows}
    if len(rows)!=len(index):
        raise ValueError("duplicate catalog row")
    audit=json.loads(a.audit.read_text())
    selected=[index[r["id"]] for r in audit["sample"]
              if r["intake_status"]=="reuse_audit_not_a_batch_job"]
    historical=[r for r in rows if r["provenance"]["kind"]=="binding_inventory"]
    print(json.dumps({"schema":"commons.proofbridge.reuse_report.v1","sample":group(rows,selected),
                      "historical":group(rows,historical),
                      "proof_status":"recorded_package_evidence_not_recompiled"},indent=2))


if __name__=="__main__":
    main()
