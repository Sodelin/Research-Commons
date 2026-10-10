#!/usr/bin/env python3
"""Sole-scheduler-only saved fitter transport and one downstream pipeline review.

No fitter, census, compiler, old semantic checker, or unchanged broad suite.
The owner authored/AST-checked this source without executing the exporter.
Use a fresh /dev/shm directory; preserve text evidence, not staged ELF files.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
EXPORTER = HERE / "fitted_source_request.py"
EXPORTER_SHA = "a2a7d5350d6a7cdea5a3058d8166a89b1df614d9d1d1c7a292362279d2e3c735"
OLD = ROOT / "research/2026-10-04-dot-practical-solver-recovery-1803z/01-exact-source-solver/package/runs"
CASES = (
    ("hybrid-common-sat", "0a34500daa05e241b1a37bd729bde40d6c01bd248ad27ce2a82950618d2ac0e4",
        "63d6b2242c428d98fe89c3c6e6295948026de220095a3fe852d5e66069db6591"),
    ("hybrid-independent-sat", "3e76f7ff26d8dcbf2db951cfe0498859c7cf147e3f03970186a3d44de98ed2ee",
        "0d3d30b9be0cf8ccbb9473c5fdeffd6a4c6a129fa122fff1ea0b181411dd7ef4"),
)
APP = ROOT / "applications/practical-solver/run.py"
APP_SHA = "e21c8099de6f82137f7fff046d0738d878a196a50b65bd0eaa9a73441ac4a916"
ADAPTER = HERE / "native_source_fit_component.py"
ADAPTER_SHA = "0a895c793714e3e5f38b0d9f6ae6dbc9464c5bd0dd14700677e05a9091dbde18"
BINARY_SHA = "443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00"
SAVED_TABLE = HERE / "evidence/source-fit-native-slot-20261010T221453.635194Z/cli-challenges/hybrid-common-sat-readout-file/stdout"
SAVED_TABLE_SHA = "3f21282fe0bdc8ecba4e8d4b4779ce3dfc3677bf4bccf904ff367c760b966039"
FALSE_FLAGS = ("certificate_valid", "source_admission_verified", "source_equation_provenance_verified",
    "source_observation_fit_verified", "source_provenance_verified", "selected_experiment_reproduced",
    "timed_readout_verified", "universal_native_refinement_verified", "full_solver_verified",
    "statistical_confidence_verified", "unknown_size_exclusion_verified", "provider_work_checked",
    "provider_exhaustion_verified")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


def wire(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def digest(value):
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode())


def save(path, value):
    path.write_bytes(wire(value))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--reference-python", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    receipt = {"schema": "fitted_source_request_review_v1", "status": "INCOMPLETE",
        "checks": [], "processes": [], "fitter_processes_started": 0,
        "semantic_source_checker_processes_started": 0, "compiler_processes_started": 0,
        "source_admission_verified": False, "source_observation_fit_verified": False,
        "universal_native_refinement_verified": False, "full_solver_verified": False}
    try:
        for path, expected in ((EXPORTER, EXPORTER_SHA), (APP, APP_SHA), (ADAPTER, ADAPTER_SHA),
            (args.binary, BINARY_SHA), (SAVED_TABLE, SAVED_TABLE_SHA)):
            require(sha(path.read_bytes()) == expected, "Pinned source/binary/retained table changed: " + str(path))
        spec = importlib.util.spec_from_file_location("reviewed_fitted_source_request", EXPORTER)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        origins, common = {}, None
        for name, origin_sha, request_sha in CASES:
            raw = (OLD / name / "RESULT.json").read_bytes()
            require(sha(raw) == origin_sha, name + ": legacy raw origin drift")
            raw_path = args.output / (name + ".BACKEND-RESULT.json")
            raw_path.write_bytes(raw)
            request, origin = module.export_witness(raw, 0)
            expected = (HERE / "fixtures/source-fit" / (name + ".request.json")).read_bytes()
            require(sha(expected) == request_sha and module.canonical_bytes(request, 65536, newline=True) == expected,
                name + ": transport differs from previously accepted DTO")
            require(origin["raw_backend_sha256"] == origin_sha and origin["native_request_sha256"] == request_sha,
                name + ": raw/DTO binding missing")
            require(origin["supplied_equations"] == 12 and len(request["equations"]) == 12
                and origin["original_observation_rows"] == 4 and origin["supplied_trace_arithmetic_checked"] is True,
                name + ": full shared trace or observation rows omitted")
            require(all(origin[key] is False for key in FALSE_FLAGS), name + ": transport promoted scientific scope")
            save(args.output / (name + ".request.json"), request)
            save(args.output / (name + ".origin.json"), origin)
            origins[name] = json.loads(raw)
            receipt["checks"].append({"name": name + "_lossless_saved_dto", "pass": True,
                "raw_sha256": origin_sha, "request_sha256": request_sha})
            if common is None:
                common = origins[name]

        def altered(mutator):
            value = copy.deepcopy(common)
            entry = value["entries"][value["witness_entry"]]
            mutator(value, entry)
            value["request_sha256"] = digest(value["request"])
            entry["equation_sha256"] = digest(entry["equations"])
            return value

        def accept(name, value, row=0, embedding=None, check=None):
            raw = wire(value)
            (args.output / (name + ".input.json")).write_bytes(raw)
            request, origin = module.export_witness(raw, row, embedding)
            require(all(origin[key] is False for key in FALSE_FLAGS), name + ": scientific gate changed")
            if check:
                check(request, origin)
            save(args.output / (name + ".request.json"), request)
            save(args.output / (name + ".origin.json"), origin)
            receipt["checks"].append({"name": name, "pass": True, "raw_sha256": sha(raw),
                "request_sha256": sha(module.canonical_bytes(request, 65536, newline=True))})

        def reject(name, raw, status=None, code=None, row=0, limits=None):
            if isinstance(raw, dict):
                raw = wire(raw)
            if len(raw) <= 65536:
                (args.output / (name + ".input.json")).write_bytes(raw)
            try:
                module.export_witness(raw, row, limits=limits)
            except module.TransportError as error:
                require(status is None or error.status == status, name + ": unexpected refusal status " + error.status)
                require(code is None or error.code == code, name + ": unexpected refusal code " + error.code)
                receipt["checks"].append({"name": name, "pass": True, "raw_sha256": sha(raw),
                    "status": error.status, "code": error.code, "limit": error.limit})
            else:
                raise ValueError(name + ": invalid/unsupported input was accepted")

        accept("forced_panel_counterfactual", common, row=2,
            check=lambda r, o: require(o["selected_row_relation"] == "COUNTERFACTUAL_NATURAL_ROOTED_OBSERVER"
                and o["selected_row"]["forced"] == {"site_alpha": 1} and len(r["equations"]) == 12,
                "Forced row was silently represented as its natural experiment"))
        accept("randomized_panel_counterfactual", common, row=3,
            check=lambda r, o: require(o["selected_row_relation"] == "COUNTERFACTUAL_NATURAL_ROOTED_OBSERVER"
                and o["selected_row"]["program"] == common["request"]["rows"][3]["program"]
                and r["values"][-1]["value"] == "1/3", "Randomized actions or shared old-g bank lost"))

        def rename(value, entry):
            value["request"]["taxa"] = ["public_Z", "public_A"]
            for row in value["request"]["rows"]:
                row["samples"] = {"public_Z": row["samples"]["L0"], "public_A": row["samples"]["L1"]}
            entry["graph"]["leaves"].reverse()
        accept("public_taxa_reversed_graph_leaf_list", altered(rename), embedding=[9007199254740993, 0, 17],
            check=lambda r, o: require(r["context"]["leaves"] == [3, 4]
                and r["taxon_labels"] == ["public_Z", "public_A"] and r["context"]["local_samples"] == [0, 0, 1]
                and r["context"]["global_labels"] == [9007199254740993, 0, 17]
                and r["values"][-1]["value"] == "1/3", "L_i/public taxon or exact large global-ID mapping changed"))
        accept("finite_seconds_metadata", altered(lambda v, e: v["request"]["limits"].update(seconds=30.25)),
            check=lambda r, o: require(o["original_request"]["limits"]["seconds"] == 30.25
                and type(r["limits"]["arithmetic_steps"]) is int, "Metadata float entered mathematical DTO"))
        accept("duplicate_zero_equations_preserved", altered(lambda v, e: e["equations"].extend([e["equations"][0], "0"])),
            check=lambda r, o: require(len(r["equations"]) == 14 and r["equations"][12] == r["equations"][0]
                and r["equations"][13] == {"dimension": 6, "terms": []}, "Duplicate/zero trace row removed or reordered"))

        def rootof(value, entry):
            encoded = {"kind": "algebraic", "polynomial_ascending": ["-1", "0", "2"], "real_root_index": 2}
            entry["values"]["x0"] = encoded
            entry["physical_realization"]["original_edges"][0]["survival_value"] = copy.deepcopy(encoded)
        accept("exact_rootof_preserved_unsupported", altered(rootof),
            check=lambda r, o: require(r["values"][0] == {"kind": "ALGEBRAIC", "polynomial_ascending": ["-1/1", "0/1", "2/1"], "real_root_index": 2}
                and o["native_evaluation_supported"] is False and o["supplied_trace_arithmetic_checked"] is False
                and o["native_evaluation_scope"] == "UNSUPPORTED_ALGEBRAIC_EVALUATION", "RootOf was evaluated, rounded or misindexed"))

        bad_digest = copy.deepcopy(common); bad_digest["request_sha256"] = "0" * 64
        reject("wrong_request_digest", bad_digest, "INVALID_REQUEST", "REQUEST_DIGEST")
        reject("changed_equation_with_updated_digest", altered(lambda v, e: e["equations"].__setitem__(0, "1")),
            "INVALID_REQUEST", "TRACE_NOT_SATISFIED")
        reject("unsafe_ast_call", altered(lambda v, e: e["equations"].__setitem__(0, "__import__('os').getpid()")),
            "UNSUPPORTED", "POLYNOMIAL_AST")
        reject("unknown_variable", altered(lambda v, e: e["equations"].__setitem__(0, "foreign_variable")),
            "UNSUPPORTED", "POLYNOMIAL_AST")
        reject("nonconstant_division", altered(lambda v, e: e["equations"].__setitem__(0, "1/x0")),
            "INVALID_REQUEST", "POLYNOMIAL_DIVISION")
        reject("float_ast_literal", altered(lambda v, e: e["equations"].__setitem__(0, "0.0")),
            "UNSUPPORTED", "POLYNOMIAL_AST")
        reject("ast_power_cap", altered(lambda v, e: e["equations"].__setitem__(0, "x0**65")), "UNKNOWN")
        reject("equation_precheck_limit", common, "UNKNOWN", limits={"equations": 0})
        reject("rational_operand_bits", common, "UNKNOWN", limits={"rational_bits": 1})
        reject("work_cap", common, "UNKNOWN", limits={"arithmetic_steps": 0})
        reject("native_frame_cap", altered(lambda v, e: e["equations"].__setitem__(slice(None), ["0"] * 4096)), "UNKNOWN")
        reject("origin_frame_cap", b" " * (16 * 1024 * 1024 + 1), "UNKNOWN")
        reject("ambiguous_status_no_first_sat", altered(lambda v, e: v.update(status="AMBIGUOUS_TARGET_TWO_ADMITTED_SOURCE_WITNESSES")),
            "UNSUPPORTED", "RESULT_STATUS")
        reject("identified_target_no_implicit_variant", altered(lambda v, e: v.update(status="IDENTIFIED_TARGET_COMPLETE_KNOWN_REGISTRY")),
            "UNSUPPORTED", "RESULT_STATUS")
        reject("invalid_explicit_witness_index", altered(lambda v, e: v.update(witness_entry=99)), "INVALID_REQUEST", "ENTRY_INDEX")
        reject("negative_panel", common, "INVALID_REQUEST", "PANEL_INDEX", row=-1)
        reject("panel_out_of_range", common, "INVALID_REQUEST", "PANEL_INDEX", row=4)
        reject("scope_flag_true", altered(lambda v, e: v.update(Lean_verification_claimed=True)), "INVALID_REQUEST", "RESULT_SCOPE")
        reject("float_law_probability", altered(lambda v, e: v["request"]["rows"][0]["law"][0].update(p=0.25)),
            "INVALID_REQUEST", "FLOAT_PATH")
        reject("nonfinite_elapsed", wire(common).replace(b'"elapsed_seconds":0.06604772400169168', b'"elapsed_seconds":NaN'),
            "INVALID_REQUEST", "NONFINITE")
        duplicate = wire(common).replace(b'{', b'{"schema":"duplicate",', 1)
        reject("duplicate_json_key", duplicate, "INVALID_REQUEST", "DUPLICATE_KEY")
        reject("zero_edge_duration", altered(lambda v, e: e["physical_realization"]["original_edges"][0].update(duration=0)),
            "INVALID_REQUEST", "PHYSICAL_EDGE")
        reject("changed_original_edge_order", altered(lambda v, e: e["graph"]["edges"].reverse()), "INVALID_REQUEST", "PHYSICAL_EDGE")
        reject("selected_joint_five_copies_not_split", altered(lambda v, e: v["request"]["rows"][0]["samples"]["L0"].extend(["d", "e"])), "UNKNOWN")

        # Actual CLI create-new/raw-origin replay, then precisely one existing app
        # readout pipeline. No old fitter or semantic source checker is launched.
        raw_path = args.output / "hybrid-common-sat.BACKEND-RESULT.json"
        cli_output = args.output / "exported-cli"
        def run(name, command, timeout):
            case = args.output / name; case.mkdir()
            started = time.monotonic()
            with (case / "stdout").open("xb") as stdout, (case / "stderr").open("xb") as stderr:
                process = subprocess.run(command, stdout=stdout, stderr=stderr, timeout=timeout, check=False)
            row = {"name": name, "command": command, "returncode": process.returncode,
                "elapsed_seconds": time.monotonic() - started,
                "stdout_sha256": sha((case / "stdout").read_bytes()), "stderr_sha256": sha((case / "stderr").read_bytes())}
            receipt["processes"].append(row)
            return process.returncode
        command = [sys.executable, "-B", str(EXPORTER), "--fit-result", str(raw_path), "--row-index", "0", "--output", str(cli_output)]
        require(run("cli-export", command, 30) == 0, "Exporter CLI failed on saved actual fitter witness")
        require((cli_output / "BACKEND-RESULT.json").read_bytes() == raw_path.read_bytes()
            and sha((cli_output / "SOURCE-FIT-REQUEST.json").read_bytes()) == CASES[0][2], "CLI origin/request bytes not lossless")
        before = {p.name: sha(p.read_bytes()) for p in cli_output.iterdir() if p.is_file()}
        require(run("cli-no-overwrite", command, 30) == 1, "Create-new CLI overwrote an accepted export")
        require(before == {p.name: sha(p.read_bytes()) for p in cli_output.iterdir() if p.is_file()}, "No-overwrite changed prior artifacts")
        receipt["checks"].append({"name": "cli_lossless_create_new_no_overwrite", "pass": True})
        app_output = args.output / "application"
        app_command = [sys.executable, "-B", str(APP), "source-fit-readout", "--request", str(cli_output / "SOURCE-FIT-REQUEST.json"),
            "--output", str(app_output), "--native-binary", str(args.binary), "--expected-binary-sha256", BINARY_SHA,
            "--reference-python", str(args.reference_python)]
        require(run("application-process", app_command, 180) == 0, "One lossless export→app pipeline failed")
        app = json.loads((app_output / "RESULT.json").read_bytes())
        child = json.loads((app_output / "component/RESULT.json").read_bytes())
        require(app["status"] == child["status"] == "SUPPLIED_FIT_ROOTED_LAW"
            and app["component_result"] == child, "Application/child success or embedding mismatch")
        require(child["request_sha256"] == CASES[0][2] and child["solver_called"] is True
            and child["checker_called"] is True and child["reference_checker_called"] is True
            and child["independent_all_coefficients_checked"] is True
            and child["independent_probabilities_checked"] is True, "Native/replay/reference process or whole-table binding missing")
        native = app_output / "component/NATIVE-RESULT.json"
        require(native.read_bytes() == SAVED_TABLE.read_bytes(), "Lossless transport changed the previously accepted complete rooted table")
        for key in ("certificate_valid", "source_admission_verified", "source_observation_fit_verified",
            "source_provenance_verified", "timed_readout_verified", "universal_native_refinement_verified", "full_solver_verified"):
            require(child[key] is False, "Export pipeline promoted " + key)
        receipt["checks"].append({"name": "actual_saved_fit_to_native_reference_readout", "pass": True,
            "request_sha256": CASES[0][2], "native_table_sha256": sha(native.read_bytes()),
            "rooted_rows": 3, "all_equations": 12, "selected_experiment_reproduced": False})
        for path, expected in ((EXPORTER, EXPORTER_SHA), (APP, APP_SHA), (ADAPTER, ADAPTER_SHA), (args.binary, BINARY_SHA)):
            require(sha(path.read_bytes()) == expected, "Source/binary drift during review: " + str(path))
        receipt.update(status="PASS", checks_passed=len(receipt["checks"]),
            exporter_sha256=EXPORTER_SHA, adapter_sha256=ADAPTER_SHA, launcher_sha256=APP_SHA, binary_sha256=BINARY_SHA,
            scope="Supplied legacy witness representation/trace transport and one natural rooted native/reference pipeline; no new source admission or fitter provenance.")
    except Exception as error:
        receipt.update(status="FAIL", error=str(error), checks_passed=len(receipt["checks"]))
    save(args.output / "RECEIPT.json", receipt)
    print(json.dumps({"status": receipt["status"], "checks_passed": receipt["checks_passed"],
        "receipt": str(args.output / "RECEIPT.json")}, sort_keys=True))
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
