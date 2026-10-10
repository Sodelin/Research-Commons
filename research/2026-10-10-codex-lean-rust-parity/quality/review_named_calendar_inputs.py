#!/usr/bin/env python3
"""Verify the exact three request projections without running a graph checker."""
import json
from datetime import datetime, timezone
from pathlib import Path
from review_support_join import PACKET, identity, read


def main():
    evidence = PACKET / "rust/evidence/named-calendar-source-input-capture-1"
    receipt_path = evidence / "RECEIPT.json"
    receipt = read(receipt_path)
    projection = read(evidence / "CODE-INPUTS.json")
    commons = PACKET.parents[1]
    errors = []
    for row in receipt["source_files"]:
        expected = {k: row[k] for k in ("bytes", "sha256")}
        if identity(commons / row["path"]) != identity(evidence / row["captured"]) or identity(evidence / row["captured"]) != expected:
            errors.append("Exact raw source: " + row["path"])
    inputs = {row["fixture"]: row for row in projection["inputs"]}
    requests = []
    for row in receipt["request_inputs"]:
        original = commons / row["original"]
        captured = evidence / row["captured"]
        expected = {k: row[k] for k in ("bytes", "sha256")}
        if identity(original) != identity(captured) or identity(captured) != expected:
            errors.append("Exact raw request: " + row["fixture"])
        request = read(captured)
        context = request["context"]
        observed = {"vertices": context["vertices"], "edge_occurrences": len(context["edges"]),
            "source": [e[0] for e in context["edges"]], "target": [e[1] for e in context["edges"]],
            "root": context["root"], "taxa": len(context["leaves"]), "taxon_leaf": context["leaves"],
            "hybrid_ids": len(context["hybrids"]), "hybrid_site": [h[0] for h in context["hybrids"]],
            "parent_false": [h[1] for h in context["hybrids"]], "parent_true": [h[2] for h in context["hybrids"]]}
        code = inputs[row["fixture"]]
        matched = (observed == code["code_input"] and code["raw_request_sha256"] == row["sha256"]
                   and context == row["context"] and request["terminal"] == row["terminal"]
                   and observed["vertices"] == 2 * observed["taxa"] + 2 * observed["hybrid_ids"] - 1
                   and observed["edge_occurrences"] == 2 * observed["taxa"] + 3 * observed["hybrid_ids"] - 2)
        if not matched:
            errors.append("Original code input: " + row["fixture"])
        requests.append({"fixture": row["fixture"], "named_source": code["named_source"],
                         "sha256": row["sha256"], "exact_projection": matched})
    for path, digest in receipt["after"].items():
        if identity(commons / path)["sha256"] != digest:
            errors.append("Current capture input: " + path)
    checks = {
        "frozen_source_input_receipt": identity(receipt_path)["sha256"] == "025bf9aa31ff8762382e2144144bf47fe9620a0796531a764b432a138f8b08c4",
        "frozen_projection": identity(evidence / "CODE-INPUTS.json")["sha256"]
            == receipt["code_projection"]["sha256"] == "1a1fd1475f6ff40dd1094c9c842a41a1086e2cdb33a5d888f69daf839c903431",
        "complete_three_inputs_eleven_sources": len(requests) == 3 and len(receipt["source_files"]) == 11
            and set(inputs) == {"twoTipCalendar", "serialNegativeTips", "parallelCommonCalendar"},
        "parallel_occurrences_and_labels_preserved": inputs["parallelCommonCalendar"]["code_input"]
            == {"vertices": 5, "edge_occurrences": 5, "source": [0, 0, 2, 2, 3], "target": [1, 2, 3, 3, 4],
                "root": 0, "taxa": 2, "taxon_leaf": [1, 4], "hybrid_ids": 1, "hybrid_site": [3],
                "parent_false": [2], "parent_true": [3]},
        "capture_stable_without_execution_or_promotion": receipt["before"] == receipt["after"] and receipt["sources_stable"]
            and all(receipt[k] == 0 for k in ("compiler_invocations", "lean_invocations", "native_invocations"))
            and not receipt["compiled_executables_copied"] and not receipt["expected_output_tables_included"]
            and not receipt["new_proofs_verified"] and not receipt["full_source_admission_verified"]
            and not receipt["outer_labelled_planarity_verified"] and not receipt["native_parser_refinement_verified"],
    }
    errors.extend(k for k, v in checks.items() if not v)
    answer = {"schema": "named_calendar_exact_input_projection_root_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "checks": checks, "requests": requests,
        "receipt": identity(receipt_path), "reviewer": identity(Path(__file__)),
        "scope": "Eleven original source bodies and three raw requests retain exact bytes. Root independently regenerates source/target/root/taxon/hybrid/false-true occurrence projections and finite cardinalities for these inputs only. Two named graphs underlie three calendars; no graph decision or solver executes. Named typed decoder proofs are separately checked, and the old incomplete smoke source is only a literal predecessor.",
        "native_parser_refinement_proved": False, "full_source_admission_verified": False,
        "master_complete": False}
    (PACKET / "quality/NAMED-CALENDAR-INPUT-REVIEW.json").write_text(
        json.dumps(answer, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors, "requests": 3, "sources": 11}))
    return not answer["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
