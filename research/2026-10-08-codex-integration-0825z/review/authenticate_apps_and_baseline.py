"""Static receipt/data authentication only; no app/Bio/solver imports or calls."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PACKET = HERE.parent
sha = lambda raw: hashlib.sha256(raw).hexdigest()
read = lambda p: json.loads(p.read_bytes())
def save(name, obj):
    (HERE / name).write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")

apps = REPO / "applications"
migration = read(apps / "MIGRATION-PROVENANCE.json")
counts = {}
for item in migration["files"]:
    path = apps / item["application"] / item["path"]
    raw = path.read_bytes()
    assert sha(raw) == item["sha256"] and len(raw) == item["bytes"]
    if item["application"] == "scientific-integration":
        assert not item["copied_byte_identically"] and "newly authored" in item["origin"]
        continue
    old = subprocess.check_output(["git", "show", migration["original_private_commit"] + ":projects/" + item["application"] + "/" + item["path"]], cwd="/workspace/Research-Commons-Private")
    assert old == raw
    counts[item["application"]] = counts.get(item["application"], 0) + 1
for item in migration["public_integration_additions"]:
    raw = (apps / item["path"]).read_bytes()
    assert sha(raw) == item["sha256"] and len(raw) == item["bytes"]
assert counts == {"genealogy-compatibility-workbench": 51, "molecular-analysis": 35}
assert migration["application_source_modules_included"] and not migration["legacy_private_proof_modules_included"]
assert sha((apps / "LICENSE").read_bytes()) == "cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30"
save("APPLICATION-MIGRATION-STATIC-AUTHENTICATION.json", {"status": "SOURCE/PUBLICATION-SCOPE ACCEPT", "reviewer_ran_applications": False,
     "inherited_git_commit": migration["original_private_commit"], "inherited_byte_exact_counts": counts,
     "new_wrapper_sha256": sha((apps / "scientific-integration/run.py").read_bytes()),
     "license": "Apache-2.0 applies to owned named application code; data/dependencies/service outputs retain own terms",
     "new_origin_separate_from_inherited_commit": True, "live_activation": False})

validation = read(PACKET / "g5/PUBLIC-WRAPPER-VALIDATION.json")
local = Path("/workspace/scratch/integration-g5/public-wrapper-validation")
for rel, digest in validation["local_evidence_sha256"].items():
    assert sha((local / rel).read_bytes()) == digest
executions = read(local / "EXECUTIONS.json")
for row in executions["executions"]:
    for suffix, field in ((".stdout", "stdout_sha256"), (".stderr", "stderr_sha256")):
        assert sha((local / (row["case"] + suffix)).read_bytes()) == row[field]
    if row.get("report"):
        result_path = Path(row["report"])
        assert sha(result_path.read_bytes()) == row["report_sha256"]
        assert sha((result_path.parent / "REPORT.html").read_bytes()) == row["html_sha256"]
        result = read(result_path)
        assert result["biological_conclusion"] == "NOT_ESTABLISHED" and result["live_model_calls"] == 0
        assert not result["whole_application_lean_verified"]
        for receipt in result["receipts"]:
            assert sha((result_path.parent / (receipt["name"] + ".stdout")).read_bytes()) == receipt["stdout_sha256"]
assert len(executions["executions"]) == 9
final_validation = read(local / "FINAL-VALIDATION.json")
assert final_validation["checks_passed"] == final_validation["checks_total"] == 63
assert len(final_validation["executions"]) == 3
intermediate = read(local / "MISSING-RUNTIME-RETEST.json")
for row in [intermediate, *final_validation["executions"]]:
    output = Path(row["command"][row["command"].index("--output") + 1])
    assert sha((output / "RESULT.json").read_bytes()) == row["result_sha256"]
    assert sha((output / "REPORT.html").read_bytes()) == row["html_sha256"]
    report = read(output / "RESULT.json")
    assert report["biological_conclusion"] == "NOT_ESTABLISHED" and report["live_model_calls"] == 0
    assert not report["whole_application_lean_verified"]
wrapper = (apps / "scientific-integration/run.py").read_bytes()
visible_line = b"            '<p><b>Execution status: ' + html.escape(result.get('status', 'UNKNOWN')) + '</b></p>'\n"
assert wrapper.count(visible_line) == 1
assert sha(wrapper.replace(visible_line, b"")) == validation["final_frozen_wrapper"]["wrapper_sha256"] == "7d41762c3594e39ea37658e063cb69ae8b318e1cd1652e34a2da5ee65ce90230"
status_controls = read(PACKET / "REPORT-STATUS-VALIDATION.json")
assert sha(wrapper) == status_controls["source_sha256"] == "86adcf3969fb85a2707fc1e40b393977a358e4989aaf090441e894f7549efbee"
for row in status_controls["rows"]:
    output = Path(row["command"][row["command"].index("--output") + 1])
    assert sha((output / "RESULT.json").read_bytes()) == row["result_sha256"]
    assert "Execution status: " + row["status"] in (output / "REPORT.html").read_text()
    assert read(output / "RESULT.json")["status"] == row["status"]
save("WRAPPER-VALIDATION-STATIC-AUTHENTICATION.json", {"status": "SOURCE + INSPECTED ACTUAL OFFLINE RECEIPTS ACCEPT", "reviewer_ran_wrapper": False,
     "initial_commands": 9, "intermediate_commands": 1, "final_predecessor_commands": 3,
     "functional_predecessor_sha256": validation["final_frozen_wrapper"]["wrapper_sha256"], "current_sha256": sha(wrapper),
     "exact_derivative": "one additional visible execution-status HTML line; removal recovers predecessor SHA exactly",
     "current_targeted_report_checks": 2, "failure_status_visible": True, "local_evidence_identity_count": len(validation["local_evidence_sha256"]),
     "biological_conclusion": "NOT_ESTABLISHED", "live_model_calls": 0, "scope": "offline plumbing/catalogue/mock/descriptive baseline; not source/data/calibration or full application proof"})

g = PACKET / "g6/REAL-BASELINE"
manifest, comparison = read(g / "MANIFEST.json"), read(g / "COMPARISON.json")
raw = (g / "GENBANK-RAW-15.gb").read_bytes()
assert sha(raw) == manifest["public_source"]["raw_sha256"] == "7a021f7abf24beb5a8c692b4e53ce6bd888ad1f6694380b75205a601110384dc"
assert len(raw) == manifest["public_source"]["raw_bytes"]
records = {}
for block in raw.decode().split("\n//"):
    if "\nORIGIN" not in block:
        continue
    version = re.search(r"^VERSION\s+(\S+)", block, re.M).group(1)
    assert version not in records
    header, origin = block.split("\nORIGIN", 1)
    seq = "".join(re.findall(r"[acgtn]+", origin)).upper()
    records[version] = {"sequence": seq, "header": header}
assert len(records) == 15
def fasta(path):
    result = {}
    for part in path.read_text().split(">"):
        if part:
            name, seq = part.split("\n", 1)
            result[name] = "".join(seq.split())
    return result
regions = {marker: fasta(g / (marker + ".raw-regions.fasta")) for marker in manifest["preprocessing"]}
reference = regions["plastid-rbcL"]["Tsuga_caroliniana"]
for item in manifest["specimens"]:
    name = item["original_taxon_id"]
    assert item["plastid"] in records and item["nuclear"] in records
    for accession in (item["plastid"], item["nuclear"]):
        assert re.search(r"^  ORGANISM\s+" + re.escape(item["organism"]) + r"\s*$", records[accession]["header"], re.M)
    nuclear = records[item["nuclear"]]["sequence"]
    assert nuclear == regions["nuclear-4CL1"][name]
    assert sha(nuclear.encode()) == item["nuclear_sequence_sha256"]
    region = item["plastid_region"]
    assert region["strand"] == 1
    cp = records[item["plastid"]]["sequence"]
    sequence = cp[region["start0"]:region["end0"]]
    assert sequence == regions["plastid-rbcL"][name] and sha(sequence.encode()) == item["plastid_region_sequence_sha256"]
    if region["kind"] == "DEPOSITED_CDS_ANNOTATION":
        assert re.search(r"CDS\s+" + str(region["start0"] + 1) + r"\.\." + str(region["end0"]) + r"\s*\n\s+/gene=\"rbcL\"", records[item["plastid"]]["header"])
    else:
        hits = []
        for offset in range(0, len(reference) - 40, 40):
            seed = reference[offset:offset + 40]
            start = cp.find(seed)
            while start >= 0:
                hits.append({"reference_offset0": offset, "genome_offset0": start, "candidate_start0": start - offset})
                start = cp.find(seed, start + 1)
        assert hits == region["anchors"] and len(hits) == 33
        assert {h["candidate_start0"] for h in hits} == {74466}
        assert sequence.startswith("ATG") and sequence[-3:] in {"TAA", "TAG", "TGA"}
        assert len(sequence) == 1428 and region["no_gene_annotation_in_original_record"]
        reverse = cp.translate(str.maketrans("ACGTN", "TGCAN"))[::-1]
        assert not any(reference[offset:offset + 40] in reverse for offset in range(0, len(reference) - 40, 40))
for marker, recipe in manifest["preprocessing"].items():
    aligned = fasta(g / (marker + ".aligned.fasta"))
    source = regions[marker]
    assert recipe["excluded_reference_sites"] == 0
    assert recipe["retained_reference_zero_based_positions"] == list(range(recipe["retained_sites"]))
    for row in recipe["pair_alignments"]:
        name = row["taxon"]
        assert row["coordinates"] == [[0, len(source[name])], [0, len(source[name])]]
        assert row["query_insertions_omitted"] == row["reference_positions_without_query_base"] == 0
        assert source[name] == aligned[name] and set(aligned[name]) <= set("ACGT")
        score = sum(2 if x == y else -1 for x, y in zip(source[recipe["reference"]], source[name]))
        assert score == row["score"]
    output = manifest["outputs"][marker]
    assert output["exit_code"] == output["checker_exit_code"] == 0
    assert sha((g / output["aligned_fasta"]).read_bytes()) == output["aligned_fasta_sha256"]
    assert sha((g / (marker + ".workbench-input.json")).read_bytes()) == output["input_sha256"]
    assert sha((g / output["receipt"]).read_bytes()) == output["receipt_sha256"]
    for suffix, field in ((".stdout", "stdout_sha256"), (".stderr", "stderr_sha256"), (".verify.stdout", "checker_stdout_sha256")):
        assert sha((g / (marker + suffix)).read_bytes()) == output[field]
    receipt = read(g / output["receipt"])
    input_data = read(g / (marker + ".workbench-input.json"))
    assert receipt["input_sha256"] == sha(json.dumps(input_data, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode())
    body = {k: v for k, v in receipt.items() if k != "receipt_sha256"}
    assert receipt["receipt_sha256"] == sha(json.dumps(body, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode())
    assert receipt["result"] == output["result"]
    for rel, digest in receipt["engine_files_sha256"].items():
        assert sha((apps / "genealogy-compatibility-workbench/genealogy_workbench" / rel).read_bytes()) == digest
    assert read(g / (marker + ".verify.stdout"))["status"] == "PASS"
    assert receipt["result"]["evidence_tier"] == "exploratory_sequence_estimate"
    assert receipt["result"]["g6_target_certificate"].startswith("ABSTAIN")
assert comparison["chloroplast_capture_conclusion"] == "UNKNOWN" and comparison["genealogy_law_or_calibrated_confidence_region"] is None
assert not comparison["full_original_Dryad_alignments_retrieved"]
replay = read(g / "PUBLIC-APP-REPLAY.json")
assert replay["preparation_source_sha256"] == sha((PACKET / "g6/prepare_real_baseline.py").read_bytes()) == "40db93dc4550462b4d6d59e5b366245008225a11e28bfc1249e6df7a280a83be"
assert replay["replay_exit_code"] == 0 and replay["existing_output_refusal"]["exit_code"] == 1
fresh = Path(replay["replay_command"][replay["replay_command"].index("--output") + 1])
assert sha((fresh / "MANIFEST.json").read_bytes()) == replay["fresh_output_manifest_sha256"]
assert sha((fresh / "COMPARISON.json").read_bytes()) == replay["fresh_comparison_sha256"]
for name, digest in replay["existing_output_refusal"]["saved_files_before_sha256"].items():
    assert sha((g / name).read_bytes()) == digest
for marker, row in replay["marker_comparisons"].items():
    assert row["replay_exit_code"] == row["checker_exit_code"] == 0
    assert sha((fresh / (marker + ".receipt.json")).read_bytes()) == row["public_app_receipt_sha256"] == row["saved_receipt_sha256"]
    assert (fresh / (marker + ".receipt.json")).read_bytes() == (g / (marker + ".receipt.json")).read_bytes()
save("REAL-BASELINE-STATIC-AUTHENTICATION.json", {"status": "EXPLORATORY SOURCE/RECEIPT scoped ACCEPT", "reviewer_ran_phylogenetics": False,
     "raw_genbank_sha256": sha(raw), "unique_records": 15, "used_records": 8,
     "appendix1_join": "all4 cpDNA/4CL1 accession-voucher rows inspected in exact paper PDF81d19502; physical specimens not authenticated",
     "independent_raw_region_and_anchor_recount": True, "chinensis_candidate": "unannotated rbcL1428nt;33consistent40ntanchors start74466; coding-boundary check",
     "reverse_complement_anchor_hits": 0, "public_workbench_replay": "two identical receipt bytes /both verify0; existing output refuses before mutation",
     "aligned_saved_matrices": "nuclear1048/plastid1428 positions; all preserved; no gaps/omissions; source/score/coordinates recounted; optimal-uniqueness author-reported",
     "marker_results": comparison["rows"], "biological_capture": "UNKNOWN", "empirical_admission": "NOT_ADMITTED",
     "rights": "NCBI data-use boundary does not assess/transfer depositor rights; no DryadCC0/Apache claim on sequences",
     "scope": "tiny two-marker descriptive baseline, not complete paper replication, source fit, iid ancestry blocks, orthology proof or calibrated capture uncertainty"})
print(json.dumps({"migration": counts, "baseline": "15records/8used,rawregions+33anchors+2savedreceipt replays authenticated"}))
