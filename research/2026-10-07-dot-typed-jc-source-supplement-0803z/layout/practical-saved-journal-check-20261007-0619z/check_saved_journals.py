"""Three real genesis-journal replays; no producer, mocks or contractions."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import sys

BASE = Path(__file__).resolve().parent
ADAPTER = BASE.parent / "practical-typed-jc-adapter-20261007-0532z"
HOST = BASE.parent / "practical-scientific-source-public-20261007-0503z" / "package"
RUNTIME = BASE.parent / "practical-synthetic-continuation-20261007-0302z" / "runtime-layout"
CORE = BASE.parent / "practical-synthetic-continuation-20261007-0302z" / "providers" / "integration_core.py"
sys.path.insert(0, str(HOST))
sys.path.insert(0, str(ADAPTER))
from jc_history_adapter import FixedJCBridge, DOMAIN, FEATURES


def utc():
    return datetime.now(timezone.utc).isoformat()


def require(value, reason):
    if not value:
        raise AssertionError(reason)


def save(path, value):
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def main():
    started = utc()
    output = BASE / "attempt1" / "scientific"
    output.mkdir(exist_ok=False)
    summary = {"schema": "typed_genesis_saved_journal_check_v1", "started_utc": started,
               "cases": [], "status": "RUNNING", "producer_invoked": False,
               "contractor_stages_invoked": False, "mocked_checker": False,
               "scientific_localization_claimed": False, "data_confidence_certificate_issued": False}
    try:
        bridge = FixedJCBridge(RUNTIME, CORE)
        history = json.loads((BASE / "HISTORY.json").read_text())
        prepared = bridge.prepare(history)
        require(prepared.request_json == (BASE / "REQUEST.json").read_bytes(),
                "literal request differs from typed preparation")
        summary["request_sha256"] = prepared.request_sha256
        manifest = json.loads((BASE / "FROZEN-FIXTURE-IDENTITIES.json").read_text())
        require(manifest["request_sha256"] == prepared.request_sha256, "fixture request identity")
        for spec in manifest["fixtures"]:
            case = spec["case"]
            file = BASE / spec["path"]
            raw = file.read_bytes()
            require(hashlib.sha256(raw).hexdigest() == spec["sha256"] and len(raw) == spec["bytes"],
                    "frozen frame bytes changed")
            require(file.name == "state-000000-" + spec["sha256"] + ".json", "frame own hash/name")
            case_started = utc()
            result = bridge.replay(prepared, BASE / "REQUEST.json", file.parent)
            case_terminal = utc()
            save(output / (case + ".json"), result)
            check = result["checker_result"]
            require(result["status"] == "UNKNOWN_OUTER_COVER", "no localization or conflict expected")
            require(result["data_confidence_certificate_issued"] is False
                    and result["scientific_admission_verified"] is False, "unadmitted protocol scope")
            require(check["physical_cover"] == [{"id": "r", "box": DOMAIN}], "complete original domain cover")
            require({v["normalized_ratio"] for v in check["widths"].values()} == {"1"}, "whole-domain diameters")
            require(check["whole_union_width_target_met"] is False
                    and check["source_feasibility_certified"] is False
                    and check["parameter_accuracy_released"] is False
                    and check["statistical_coverage_verified"] is False, "no promoted scientific result")
            if case == "positive":
                require(result["checker_mode"] == "normal_validated", "positive complete replay mode")
                detail = check["details"]
                require(detail["complete_numeric_replay"] is True and detail["journal_frames"] == 1,
                        "one complete genesis frame")
                require(all(detail[k] == 0 for k in ("stages_started", "stages_recomputed", "splits", "exclusions")),
                        "zero contractor transitions")
                require(check["augmented_states"][0]["state"]["moments"] ==
                        {k: ["1/2", "3/4"] for k in FEATURES}, "once-only initialized units")
            else:
                require(result["checker_mode"] == "recovered_authenticated_original_domain",
                        "negative journal must fall back, not validate")
                detail = check["details"]
                reason = "fixed provenance identity" if case == "wrong-request" else "complete frontier mismatch"
                require(detail["all_inherited_narrowing_discarded"] is True
                        and detail["failure_type"] == "InvalidCertificate" and detail["reason"] == reason,
                        "semantic negative control reason")
                require(check["augmented_states"][0]["state"]["moments"] ==
                        {k: ["0", "1"] for k in FEATURES}, "fallback discards inherited moment narrowing")
            summary["cases"].append({"case": case, "started_utc": case_started,
                "terminal_utc": case_terminal, "status": "PASS", "checker_mode": result["checker_mode"],
                "frame_sha256": spec["sha256"], "output_sha256": hashlib.sha256((output / (case + ".json")).read_bytes()).hexdigest()})
        require(len(summary["cases"]) == 3, "exactly three saved-journal cases")
        summary["status"] = "PASS_GENESIS_BINDING_ONLY"
    except Exception as error:
        summary.update(status="FAILED_STOPPED_NO_RETRY", error_type=type(error).__name__, error=str(error))
        raise
    finally:
        summary["terminal_utc"] = utc()
        save(output / "SUMMARY.json", summary)
    print(json.dumps({"status": summary["status"], "cases": len(summary["cases"]),
                      "started_utc": started, "terminal_utc": summary["terminal_utc"]}))


if __name__ == "__main__":
    main()
