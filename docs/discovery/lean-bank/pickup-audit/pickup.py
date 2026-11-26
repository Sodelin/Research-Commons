"""Inert exactly-one-pickup transaction; never executes a proof job."""
import json
import sqlite3
from proof_job_ingress import binding, fields, need, digest, pinned, evaluate

def pick(db, tick, registry, rpin, ledger, lpin, queue, qpin, catalog, cpin, materials):
    """tick is trusted scheduler identity; materials are fetched bytes, not commands."""
    need(type(tick) is int and tick >= 0, "bad scheduler tick")
    q = pinned(queue, qpin, "queue")
    c = pinned(catalog, cpin, "catalog")
    fields(q, "schema", "registry_sha256", "ledger_sha256", "catalog_sha256", "entries")
    fields(c, "schema", "entries")
    need(q["schema"] == "proofbridge.pickup-queue.v1" and
         c["schema"] == "proofbridge.pickup-catalog.v1", "wrong input schema")
    need((q["registry_sha256"], q["ledger_sha256"], q["catalog_sha256"]) ==
         (rpin, lpin, cpin), "mixed snapshot")
    need(type(q["entries"]) is list and len(q["entries"]) <= 128 and
         type(c["entries"]) is list and len(c["entries"]) <= 128, "bad queue/catalog limit")
    rows = {}
    for row in c["entries"]:
        fields(row, "job", "commit", "source_sha256", "statement_sha256",
               "lean_receipt_ref", "lean_output_sha256")
        ident = binding(row)
        need(ident not in rows, "duplicate catalog binding")
        rows[ident] = row
    with sqlite3.connect(db, isolation_level=None, timeout=5) as cx:
        cx.execute("CREATE TABLE IF NOT EXISTS picks(tick INTEGER PRIMARY KEY, binding TEXT UNIQUE, receipt TEXT NOT NULL)")
        cx.execute("BEGIN IMMEDIATE")
        prior = cx.execute("SELECT receipt FROM picks WHERE tick=?", (tick,)).fetchone()
        if prior:
            cx.commit()
            return {"status":"already_picked", "receipt":json.loads(prior[0])}
        for entry in q["entries"]:
            fields(entry, "job", "commit", "source_sha256", "statement_sha256", "request_sha256")
            ident = binding(entry)
            key = json.dumps(ident, separators=(",", ":"))
            if cx.execute("SELECT 1 FROM picks WHERE binding=?", (key,)).fetchone():
                continue
            need(ident in rows and ident in materials, "missing exact catalog or source binding")
            request, source = materials[ident]
            need(entry["request_sha256"] == digest(request), "request bytes mismatch")
            ev = evaluate(registry, rpin, ledger, lpin, request, source)
            need(binding(ev) == ident, "request substituted another registered theorem")
            need(ev["disposition"] == "trusted_kernel_receipt_matched", "no complete registry evidence")
            lean = ev["stages"]["lean"]
            row = rows[ident]
            need((lean["receipt_ref"], lean["output_sha256"]) ==
                 (row["lean_receipt_ref"], row["lean_output_sha256"]), "catalog references different evidence")
            receipt = {"schema":"proofbridge.one-pickup.v1", "tick":tick,
                       **{k:ev[k] for k in ("job","commit","source_sha256","statement_sha256")},
                       "queue_sha256":qpin, "catalog_sha256":cpin,
                       "registry_sha256":rpin, "ledger_sha256":lpin,
                       "lean_receipt_ref":lean["receipt_ref"],
                       "lean_output_sha256":lean["output_sha256"],
                       "fresh_checker_execution":False}
            cx.execute("INSERT INTO picks VALUES (?,?,?)", (tick,key,json.dumps(receipt,sort_keys=True)))
            cx.commit()
            return {"status":"picked_existing_receipt","receipt":receipt}
        cx.commit()
        return {"status":"no_work"}
