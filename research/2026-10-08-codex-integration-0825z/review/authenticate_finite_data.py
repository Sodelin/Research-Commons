"""Independent static recount only; no owner scientific code imported/executed."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
P = HERE.parent / "practical"
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_bytes())
fd = P / "finite-data"
r = read(fd / "RESULT.json")
original = REPO / "research/2026-10-05-dot-msci-generated-phased-model-check-1854z"
for rel, digest in r["input_pins"].items():
    assert sha((original / rel).read_bytes()) == digest
data = read(original / "integration/declared-model/DATASET.json")
extraction = read(fd / "EXTRACTION.json")
assert len(data["loci"]) == extraction["m"] == r["loci"] == 1024
counts = dict.fromkeys(extraction["feature_order"], 0)
chi = {"A": 1, "C": 1, "G": -1, "T": -1}
selection = []
for locus in data["loci"]:
    selection.append({"id": locus["id"], "columns": locus["columns"]})
    for key in counts:
        x, y = extraction["pairs"][key[:2]]
        parity = 1
        for site in range(int(key[-1])):
            parity *= chi[locus["calls"][x][site]] * chi[locus["calls"][y][site]]
        counts[key] += (1 + parity) // 2
assert counts == extraction["counts"] == r["counts"]
assert sha((json.dumps(selection, sort_keys=True, separators=(",", ":")) + "\n").encode()) == extraction["selection_sha256"]
confidence = read(fd / "CONFIDENCE.json")
assert confidence == read(original / "integration/composition-attempt1/prepared/CONFIDENCE.json")
radius = Q(confidence["radius"])
assert radius == Q(3301, 65536)
means = {key: [str(max(Q(0), Q(n, 1024) - radius)), str(min(Q(1), Q(n, 1024) + radius))] for key, n in counts.items()}
assert means == confidence["shifted_mean_box"] == read(fd / "REQUEST.json")["features"]
conversion = read(fd / "MEAN-CONVERSION.json")
converted = {key: [str(max(Q(0), 2 * Q(lo) - 1)), str(min(Q(1), 2 * Q(hi) - 1))] for key, (lo, hi) in means.items()}
assert conversion["actual"] == conversion["expected"] == converted
lo, hi, accepted = Q(0), Q(1), None
for row in confidence["search"]:
    candidate = (lo + hi) / 2
    assert Q(row["radius"]) == candidate
    assert Q(row["exponent"]) == 2 * 1024 * candidate * candidate
    assert Q(row["union_error_upper"]) == 18 * Q(row["exp_interval"][1])
    passed = Q(row["union_error_upper"]) <= Q(1, 10)
    assert row["certified"] == passed
    if passed:
        hi = accepted = candidate
    else:
        lo = candidate
assert accepted == radius and Q(confidence["error_upper_bound"]) <= Q(1, 10)
request = read(fd / "REQUEST.json")
checker = read(fd / "checker.stdout")
assert checker == r["checker"] and checker["status"] == "UNKNOWN_OUTER_COVER"
assert checker["details"]["complete_numeric_replay"]
assert checker["details"]["stages_recomputed"] == 23 and checker["details"]["journal_frames"] == 50 and checker["details"]["splits"] == 1
for stage, receipt in zip(("producer", "checker"), r["executions"]):
    assert receipt["exit_code"] == 0 and not receipt["timeout"]
    assert sha((fd / (stage + ".stdout")).read_bytes()) == receipt["stdout_sha256"]
    assert sha((fd / (stage + ".stderr")).read_bytes()) == receipt["stderr_sha256"]
for row in r["journal"]:
    raw = (fd / "journal" / row["name"]).read_bytes()
    assert sha(raw) == row["sha256"] and len(raw) == row["bytes"]
for key, width in checker["widths"].items():
    union = max(Q(c["box"][key][1]) for c in checker["physical_cover"]) - min(Q(c["box"][key][0]) for c in checker["physical_cover"])
    domain = Q(request["box"][key][1]) - Q(request["box"][key][0])
    assert union == Q(width["width"]) and union / domain == Q(width["normalized_ratio"]) == 1
witness = read(fd / "PAIR-WIDTH-OBSTRUCTION.json")
archive_raw = (REPO / "research/2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json").read_bytes()
assert sha(archive_raw) == witness["source_mean_archive_sha256"]
archive = json.loads(archive_raw)
assert archive["source_parameter_points"] == witness["source_parameter_points"]
for point in archive["source_parameter_points"]:
    for key, value in point.items():
        assert Q(request["box"][key][0]) <= Q(value[0]) == Q(value[1]) <= Q(request["box"][key][1])
for point_means in archive["source_forward_mean_boxes"]:
    for key, (a, b) in point_means.items():
        assert Q(means[key][0]) <= Q(a) <= Q(b) <= Q(means[key][1])
separation = abs(Q(witness["source_parameter_points"][0]["rA"][0]) - Q(witness["source_parameter_points"][1]["rA"][0])) / (Q(6) - Q(1, 2))
assert separation == Q(witness["normalized_rA_separation"]) == Q(3, 55) > Q(1, 20)
cli = P / "cli-finite-record"
diagnostic = read(cli / "NATIVE-DIAGNOSTIC.json")
assert diagnostic["all_complete_cover_cells_consumed"] == 2 and diagnostic["ordered_pairs"] == 4
assert not diagnostic["conditional_pair_geometry_all_pass"] and diagnostic["exact_fields_match"]
for row, case, expected in zip((cli / "native-pairs.stdout").read_text().splitlines(), diagnostic["cases"], diagnostic["python_expected"]):
    fields = row.split("\t")
    assert len(fields) == 16 and fields[:5] == ["result", case["id"], "UNKNOWN", "PULSE_DENOMINATOR", "2"]
    assert fields[10:] == ["0"] * 6
    assert expected["status"] == fields[2] and expected["refusal"] == fields[3] and expected["scalar_exp_calls"] == int(fields[4])
refusal = read(P / "cli-model-mismatch/RESULT.json")
assert refusal["status"] == "MODEL_NOT_ADMITTED" and not refusal["native_or_numerical_solver_called"]
adjudication = read(P / "post-checker-native/ADJUDICATION.json")
assert sha((P / "post-checker-native/RESULT.json").read_bytes()) == adjudication["original_result_sha256"]
assert Q(adjudication["boundary_normalized_upper"]) - Q(1, 20) == Q(adjudication["boundary_overshoot_above_1_20"]) > 0
v2 = P / "cli-finite-record-loader-v2"
v2result, helpers = read(v2 / "RESULT.json"), read(v2 / "EXECUTED-HELPERS.json")
assert v2result["program_sha256"] == sha((P / "pipeline.py").read_bytes()) == "897fb28e37a34719314103827f30e3baa64cd6045b8c7dc16746a5fb27f5d1c6"
assert v2result["executed_helper_sources"] == helpers
for identity in helpers.values():
    raw = Path(identity["path"]).read_bytes()
    assert sha(raw) == identity["sha256"] and len(raw) == identity["bytes"]
    assert identity["execution"] == "compile_exec_verified_single_read_bytes"
assert sha((P / "cli-loader-before/pipeline.py").read_bytes()) == "2a799c36b8cf4dcf1d1389e843731e2c939fa4bc4d46129d429a5d0c8e09279a"
v2checker = read(v2 / "checker.stdout")
assert v2checker == v2result["original_complete_checker"]
assert v2checker["details"]["complete_numeric_replay"] and v2checker["details"]["stages_recomputed"] == 23 and v2checker["details"]["journal_frames"] == 50
assert all(Q(x["normalized_ratio"]) == 1 for x in v2checker["widths"].values())
for stage, execution in zip(("producer", "checker"), v2result["executions"]):
    assert execution["exit_code"] == 0 and not execution["timeout"]
    assert sha((v2 / (stage + ".stdout")).read_bytes()) == execution["stdout_sha256"]
v2diagnostic = read(v2 / "NATIVE-DIAGNOSTIC.json")
assert v2diagnostic["native_actual"] == diagnostic["native_actual"] and v2diagnostic["python_expected"] == diagnostic["python_expected"]
assert v2diagnostic["ordered_pairs"] == 4 and v2diagnostic["exact_fields_match"] and v2diagnostic["source_and_binary_unchanged"]
assert (v2 / "native-pairs.stdout").read_bytes() == (cli / "native-pairs.stdout").read_bytes()
controls = read(P / "logs/AUTHENTICATED-LOADER-CONTROLS.json")
assert controls["pipeline_program_sha256"] == v2result["program_sha256"]
assert controls["status"] == "PASS" and controls["old_timestamp_loader_value"] == 1 and controls["verified_single_buffer_value"] == 2
assert controls["substituted_source_refused_before_exec"] and controls["substituted_module_not_registered"]
v2refusal = read(P / "cli-model-mismatch-loader-v2/RESULT.json")
assert v2refusal["status"] == "MODEL_NOT_ADMITTED" and not v2refusal["native_or_numerical_solver_called"]
out = {"status": "STATIC RECOUNT + INSPECTED AUTHOR RECEIPT ACCEPT", "reviewer_executed_scientific_code": False,
       "loci": 1024, "literal_counts": counts, "radius": str(radius), "once_only_mean_conversion": True,
       "frames": 50, "stages": 23, "splits": 1, "all9_normalized_full_union_widths": "1",
       "normalized_rA_compatible_point_separation": str(separation), "width_obstruction_scope": witness["scope"],
       "native_pairs": "all4 ordered complete-cell pairs UNKNOWN/PULSE_DENOMINATOR; exact backend agreement",
       "rounding_adjudication": "strictly above1/20; prior harness failure preserved; no backend mismatch",
       "scientific_confidence_admitted": False, "fresh_generation": False, "parameter_accuracy_released": False,
       "pipeline_import_identity": "corrected897fb28e helper loader executes one captured fixed-hash buffer; earlier source/receipts retained",
       "helper_loader_actual_controls": "effective timestamp-valid stale-pyc countercontrol plus substituted-source refusal",
       "minimal_v2_rerun": "same23stages50frames/all9width1/four identical UNKNOWN pairs; no-build"}
(HERE / "FINITE-DATA-STATIC-AUTHENTICATION.json").write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
print(json.dumps({"static_recount": "1024 loci /9counts", "full_union": "all9 width1", "rA_obstruction": "3/55", "native": "4/4 UNKNOWN agreement"}))
