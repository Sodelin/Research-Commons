"""One real existing nontrivial replay; mismatch guards do not call the checker."""
from copy import deepcopy
from datetime import datetime, timezone
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import sys

BASE = Path(__file__).resolve().parent
ADAPTER = BASE.parent / "practical-typed-jc-adapter-20261007-0532z"
HOST = BASE.parent / "practical-scientific-source-public-20261007-0503z" / "package"
RUNTIME = BASE.parent / "practical-synthetic-continuation-20261007-0302z" / "runtime-layout"
CORE = BASE.parent / "practical-synthetic-continuation-20261007-0302z" / "providers" / "integration_core.py"
LEGACY = BASE.parent / "practical-existing-journal-audit-20261007-0640z"
sys.path.insert(0, str(HOST))
sys.path.insert(0, str(ADAPTER))
from jc_history_adapter import FixedJCBridge, DOMAIN
from legacy_alias import ExistingJournalAlias, CompatibilityError, OLD_REQUEST_SHA


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
    out = BASE / "attempt1" / "scientific"
    out.mkdir(exist_ok=False)
    summary = {"schema": "one_existing_journal_alias_check_v1", "started_utc": utc(),
               "status": "RUNNING", "controls": [], "producer_invoked": False,
               "new_data_acquired": False, "new_statistical_events": 0}
    try:
        bridge = FixedJCBridge(RUNTIME, CORE)
        alias = ExistingJournalAlias(bridge, LEGACY)
        history = json.loads((BASE / "ALIAS-HISTORY.json").read_text())
        prepared = bridge.prepare(history)
        require(prepared.request_sha256 != OLD_REQUEST_SHA, "old and new request identities remain distinct")
        with (out / "PREPARED-TYPED-REQUEST.json").open("xb") as stream:
            stream.write(prepared.request_json)
        # Pure guard controls: the fixed old request/journal is never altered.
        changed_feature = deepcopy(history)
        old_lower = Q(changed_feature["blocks"][0]["shifted_mean_box"]["AA1"][0])
        changed_feature["blocks"][0]["shifted_mean_box"]["AA1"][0] = str(old_lower + Q(1, 65536))
        changed_delta = deepcopy(history)
        changed_delta["error_budget"] = "1/20"
        changed_delta["blocks"][0]["error_allowance"] = "1/20"
        for name, control, expected in (("changed-feature", changed_feature, "feature interval mismatch"),
                                        ("changed-delta", changed_delta, "delta mismatch")):
            save(out / (name + ".json"), control)
            rejected = False
            try:
                alias.assert_compatible(bridge.prepare(control))
            except CompatibilityError as error:
                require(str(error) == expected, "wrong mismatch-control rejection")
                rejected = True
            require(rejected and alias.checker_calls == 0, "mismatch reached numerical checker")
            summary["controls"].append({"name": name, "status": "REJECTED_BEFORE_CHECKER", "reason": expected})
        replay_started = utc()
        result = alias.replay_equivalent(prepared)
        replay_terminal = utc()
        save(out / "ALIAS-RESULT.json", result)
        check = result["checker_result"]
        require(alias.checker_calls == result["checker_calls"] == 1, "exactly one actual checker invocation")
        require(result["validated_legacy_request_sha256"] == OLD_REQUEST_SHA
                and result["prepared_request_sha256"] == prepared.request_sha256,
                "legacy/typed request identities")
        require(result["new_request_claimed_as_replayed"] is False
                and result["old_request_or_journal_reserialized"] is False, "no hash relabelling")
        require(result["legacy_delta"] == "1/10" and result["new_statistical_events"] == 0
                and result["data_confidence_certificate_issued"] is False
                and result["data_confidence_certificate_eligible"] is False
                and result["finite_generator_law_certified"] is False, "historical statistical scope")
        require(check["mode"] == "normal_validated" and check["details"]["complete_numeric_replay"] is True,
                "complete original replay")
        require(check["details"]["journal_frames"] == 24
                and check["details"]["stages_recomputed"] == 11
                and check["details"]["stages_started"] == 11
                and check["details"]["authenticated_journal_bytes"] == 208722,
                "exact nontrivial journal scope")
        require(check["physical_cover"] == [{"id": "r", "box": DOMAIN}]
                and {v["normalized_ratio"] for v in check["widths"].values()} == {"1"}
                and check["whole_union_width_target_met"] is False
                and check["source_feasibility_certified"] is False, "unchanged full-domain UNKNOWN")
        summary.update(status="PASS_EXISTING_NONTRIVIAL_ALIAS_ONLY", checker_calls=1,
                       replay_started_utc=replay_started, replay_terminal_utc=replay_terminal,
                       validated_legacy_request_sha256=OLD_REQUEST_SHA,
                       prepared_request_sha256=prepared.request_sha256,
                       journal_frames=24, stages_recomputed=11,
                       physical_localization_improved=False,
                       result_sha256=hashlib.sha256((out / "ALIAS-RESULT.json").read_bytes()).hexdigest())
    except Exception as error:
        summary.update(status="FAILED_STOPPED_NO_RETRY", error_type=type(error).__name__, error=str(error))
        raise
    finally:
        summary["terminal_utc"] = utc()
        save(out / "SUMMARY.json", summary)
    print(json.dumps({"status": summary["status"], "checker_calls": 1,
                      "started_utc": summary["started_utc"], "terminal_utc": summary["terminal_utc"]}))


if __name__ == "__main__":
    main()
