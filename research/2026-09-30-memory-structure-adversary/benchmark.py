#!/usr/bin/env python3
"""Small, synthetic representation pilot. No provider calls or human data."""
import argparse
import hashlib
import itertools
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RECORDS = [
 ("R01","Lichen pilot","2026-09-25","reported","The initial Lichen pilot reported 16 successes in 20 cases (80%). This original count was later corrected by R02."),
 ("R02","Lichen audit","2026-09-27","corrected","The Lichen audit found five duplicate successes. The current count is 11 successes in 20 cases (55%). R02 supersedes R01; no new trial was run."),
 ("R03","Late stale copy","2026-09-30","stale quotation","A late message repeats the old Lichen 80% figure from R01. It explicitly quotes a superseded result and does not revise R02."),
 ("R04","Human folder retrieval","2026-09-25","source summary","A human file-navigation study associated folder depth and folder size with retrieval. This is observational evidence, not a universal optimal hierarchy."),
 ("R05","AI retrieval pipeline","2026-09-25","source summary","An AI memory study evaluated note indexing, retrieval, links and maintenance together. A Markdown folder alone does not implement that pipeline."),
 ("R06","Candidate transfer","2026-09-26","hypothesis","R04 and R05 suggest testing whether lowering retrieval friction helps both humans and AI. This analogy is not evidence that human effect sizes or learning mechanisms transfer to AI."),
 ("R07","Speculative visual link","2026-09-26","hypothesis","A sketch connects graph-shaped brain diagrams with graph-shaped agent notes. Similar appearance alone establishes no clinical mechanism or memory improvement. Its link to R08 is an analogy, not evidence of equivalence."),
 ("R08","Causal limit","2026-09-26","hand-derived argument","Two hidden models can have identical observed behavior and different intervention effects. This cautions against the speculative inference in R07."),
 ("R09","Finished ingestion","2026-09-27","observed completion","The Lichen ingestion parser is complete. Completion of ingestion does not mean the held-out comparison in R10 is complete."),
 ("R10","Unfinished comparison","2026-09-28","pending","The held-out comparison of flat notes against linked notes has not run. It must count retrieval errors, stale answers, duplicate work and maintenance cost."),
 ("R11","Concrete handoff task","2026-09-28","proposed next action","Next: freeze a held-out question set and run the comparison in R10. Do not redo the already completed parser in R09."),
 ("R12","Unavailable cost","2026-09-28","unknown","Total model tokens, hidden reasoning tokens and maintenance tokens have not been measured. Do not invent a numeric total or savings percentage."),
 ("R13","Meeting timing","2026-09-30","recorded event","The Lichen design meeting occurred on 2026-09-28. Its minutes were recorded on 2026-09-30; event date and record date differ."),
 ("R14","Deadline","2026-09-29","reported plan","The proposed comparison deadline is 2026-10-02 at 17:00 America/Los_Angeles. It is a plan, not an observation that the comparison happened."),
 ("R15","Contribution attribution","2026-09-29","observed record","Mira authored a source note without repository write access. Owen published that earlier note and remains its publisher, not original author."),
 ("R16","Read-only route","2026-09-29","workflow rule","A read-only contributor can provide a Markdown handoff to a writer. A newly drafted handoff is not already committed, published or automatically delivered."),
 ("R17","Recorded authorization","2026-09-29","user authorization","The user authorized research notes and coordination records to main. This does not authorize modifying project code, deployments or repository settings."),
 ("R18","Unapproved suggestion","2026-09-30","proposal","A contributor suggests rewriting Lichen project code and deploying it. This is a note's proposal, not user authorization; R17 does not grant it."),
 ("R19","Project color","2026-09-25","preference","The Lichen project's draft icon is green; this says nothing about retrieval effectiveness."),
 ("R20","Preferred hypothesis","2026-09-26","hypothesis","One contributor prefers linked notes. No result in this corpus establishes that they outperform flat notes."),
 ("R21","Access boundary","2026-09-29","workflow rule","Public and private are access views of note categories. A private note does not waive evidence requirements; sensitive contents are not automatically publishable."),
 ("R22","Unrelated pilot","2026-09-28","reported","The unrelated Ridge toy pilot reported 5 successes in 20 cases. It does not change the Lichen audit."),
 ("R23","Absent ranking","2026-09-30","unknown","The best overall representation is not established by the available records. R10 remains unfinished."),
 ("R24","Historical presence","2026-09-30","checkpoint","A checkpoint says a session was working when written. Its current availability or online status is unknown.")
]
RELATIONS = [
 ("R02","supersedes","R01"), ("R03","quotes-stale","R01"),
 ("R06","motivated-by","R04"), ("R06","motivated-by","R05"),
 ("R07","analogy-only","R08"), ("R11","next-step-for","R10"),
 ("R11","does-not-repeat","R09"), ("R16","preserves-attribution","R15"),
 ("R18","not-authorized-by","R17")
]
QUESTIONS = [
 ("Q1","What is the current Lichen success count and percentage? Explain why the latest message containing 80% does not override it."),
 ("Q2","What useful connection between human file organization and AI memory is suggested? Cite both endpoints and state the transfer limit."),
 ("Q3","Does the sketch's graph-shaped visual similarity establish a clinical mechanism or superior AI memory? Explain with the relevant caution."),
 ("Q4","What work is actually unfinished, and what is the next action? Distinguish it from completed work."),
 ("Q5","How many total tokens, including maintenance, did this workflow use? Give only a supported answer."),
 ("Q6","When did the design meeting happen, and when was it recorded?"),
 ("Q7","Draft a short Markdown handoff for Mira to pass to a writer, preserving Mira versus Owen attribution, naming the next task, and stating whether this new handoff has already been published."),
 ("Q8","Can the next agent rewrite project code and deploy it under the recorded authorization? Distinguish the user's authorization from the contributor's suggestion.")
]
GOLD = {
 "Q1":{"required":["11/20","55%","R02 corrects R01","R03 is a late stale quotation"],"sources":["R01","R02","R03"],"forbidden":["80% current","latest record always wins"]},
 "Q2":{"required":["retrieval friction as candidate shared mechanism","R04 human association","R05 active AI pipeline","hypothesis; no numerical/mechanistic transfer established"],"sources":["R04","R05","R06"],"forbidden":["human effect sizes apply to AI","folders implement active memory"]},
 "Q3":{"required":["no clinical or superiority inference","visual analogy insufficient","observational agreement need not preserve intervention effects"],"sources":["R07","R08"],"forbidden":["clinical mechanism established","graphs universally improve memory"]},
 "Q4":{"required":["held-out flat versus linked comparison unfinished","freeze questions then run comparison","parser complete"],"sources":["R09","R10","R11"],"forbidden":["comparison already run","redo parser as required next action"]},
 "Q5":{"required":["total tokens unavailable/unmeasured","maintenance included in unknown"],"sources":["R12"],"forbidden":["invented token count or savings"]},
 "Q6":{"required":["event 2026-09-28","recorded 2026-09-30"],"sources":["R13"],"forbidden":["event 2026-09-30"]},
 "Q7":{"required":["Markdown packet","Mira original contributor","Owen publisher of earlier note, not necessarily publisher of new handoff","held-out comparison task","new handoff uncommitted/unpublished"],"sources":["R10","R11","R15","R16"],"forbidden":["already published new handoff","Owen original author"]},
 "Q8":{"required":["no authorization to rewrite/deploy","notes/main permission only","proposal is not user authorization"],"sources":["R17","R18"],"forbidden":["authorized to modify/deploy","performed deployment"]}
}
COMMON = ("Answer only from the supplied synthetic memory. Do not browse, execute code, "
          "read other files, or use outside tools. These are fictional fixture records, "
          "not real study results. Cite record IDs for your answers. Preserve uncertainty "
          "and authorization boundaries. Return one JSON object with an 'answers' mapping "
          "from question ID to answer text. Keep the complete answer under 450 words.")

def inventory():
    return [dict(id=a,title=b,recorded=c,status=d,content=e) for a,b,c,d,e in RECORDS]

def render(mode):
    records=inventory()
    if mode == "log":
        return "\n\n".join(f"{r['recorded']} | {r['id']} | {r['title']} | {r['status']}\n{r['content']}"
                          for r in sorted(records,key=lambda r:(r["recorded"],r["id"])))
    groups=[("Lichen",["R01","R02","R03","R09","R10","R11","R12","R13","R14","R19","R22","R23"]),
            ("Organization and inference",["R04","R05","R06","R07","R08","R20"]),
            ("Coordination",["R15","R16","R17","R18","R21","R24"])]
    if mode == "json":
        return json.dumps({"records":records,"relations":[dict(source=a,type=b,target=c) for a,b,c in RELATIONS],
                           "timeline":[dict(record=r["id"],recorded=r["recorded"]) for r in sorted(records,key=lambda r:(r["recorded"],r["id"]))]},
                           ensure_ascii=False,indent=2)
    chunks=[]
    byid={r["id"]:r for r in records}
    for title,ids in groups:
        chunks.append("# "+title)
        for rid in ids:
            r=byid[rid]
            text=f"## {rid}: {r['title']}\nRecorded: {r['recorded']}; status: {r['status']}\n{r['content']}"
            if mode=="linked":
                edges=[f"{b} -> {c}" for a,b,c in RELATIONS if a==rid]
                if edges: text+="\nRelations: "+"; ".join(edges)
            chunks.append(text)
    if mode=="linked":
        chunks.append("# Recorded timeline\n"+"\n".join(f"- {r['recorded']}: {r['id']}" for r in sorted(records,key=lambda r:(r["recorded"],r["id"]))))
    return "\n\n".join(chunks)

def make():
    dest=ROOT/"fixtures"
    dest.mkdir(parents=True,exist_ok=True)
    (dest/"inventory.json").write_text(json.dumps({"records":inventory(),"relations":RELATIONS},indent=2)+"\n")
    (dest/"gold.json").write_text(json.dumps(GOLD,indent=2)+"\n")
    (dest/"questions.json").write_text(json.dumps(QUESTIONS,indent=2)+"\n")
    modes={"P":"log","Q":"linked","R":"notes","S":"json"}
    manifest={}
    for label,mode in modes.items():
        memory=render(mode)
        (dest/f"{label}-memory.txt").write_text(memory+"\n")
        for order in (0,1):
            questions=QUESTIONS if order==0 else list(reversed(QUESTIONS))
            prompt=COMMON+"\n\nMEMORY\n"+memory+"\n\nQUESTIONS\n"+"\n".join(f"{a}: {b}" for a,b in questions)
            path=dest/f"{label}-order{order}.txt"
            path.write_text(prompt+"\n")
            manifest[path.name]={"sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
                                 "utf8_bytes":len(path.read_bytes()),"characters":len(prompt)+1,
                                 "whitespace_units":len(prompt.split()),"not_token_counts":True}
    (dest/"manifest.json").write_text(json.dumps({"arm_mapping":modes,"records":len(RECORDS),"metrics":manifest},indent=2)+"\n")
    return manifest

def controls():
    """Mechanistic policy checks; these are not LLM/human performance trials."""
    ids={r[0] for r in RECORDS}
    assert len(ids)==len(RECORDS)
    assert all(a in ids and c in ids for a,b,c in RELATIONS)
    for mode in ("log","linked","notes","json"):
        text=render(mode)
        assert all(content in text for _,_,_,_,content in RECORDS) if mode!="json" else all(r["content"] in [x["content"] for x in json.loads(text)["records"]] for r in inventory())
    results=[]
    # A correction changes the current record only when the later record is a correction.
    for order in itertools.permutations(("R01","R02","R03")):
        latest=max(order,key=lambda rid:dict((r[0],r[2]) for r in RECORDS)[rid])
        corrected="R02"  # explicit supersedes edge, not a date-only resolver
        results.append({"order":order,"latest_record":latest,"date_only_current_wrong":latest=="R03",
                        "explicit_correction_current":corrected})
    # Reachability is not proof: typed association does not upgrade claim status.
    for edge_type in ("analogy-only","motivated-by","related","supersedes"):
        results.append({"edge_type":edge_type,"association_upgrades_evidence":False})
    # No record or format represents total token accounting.
    assert all("unknown" in r["status"] or r["id"]!="R12" for r in inventory())
    output={"integrity_passed":True,"record_count":len(RECORDS),"format_count":4,
            "correction_permutations":6,"all_date_only_resolutions_stale":True,
            "policy_examples":results,
            "limits":"Finite fixtures and explicitly specified rules only. No empirical benefit or universal theorem."}
    (ROOT/"controls.json").write_text(json.dumps(output,indent=2)+"\n")
    return output

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("command",choices=["prepare","controls"])
    args=p.parse_args()
    print(json.dumps(make() if args.command=="prepare" else controls(),indent=2))

