"""One public legacy journal, checked under its OLD identity and exact set alias.

No producer, reserialization of the original request, or admission upgrade.
"""
from pathlib import Path
import hashlib
import json

from genealogy_workbench.core import InputError
from genealogy_workbench.provenance import digest
from jc_history_adapter import CORE_SHA, DOMAIN, FEATURES, MAP, MODEL, PHYSICAL, QUANTITY

LEGACY_MANIFEST_SHA = "dfdfe1a36c9be8c2a80078958ecb2caa870552be9781ab23ba9185c1d0215145"
OLD_REQUEST_SHA = "a011e2369224bf4de82990be0eca622e8676c8d8d8addd9e1e757ac01f6a82f3"
OLD_COMPOSED_SHA = "0cb183855156b02cc235cb886ba5eef8c236007d7ed177bca2bff80745f96dc7"
OLD_COMMIT = "5e01a8e727478a2f22686d31f71304126e345116"


class CompatibilityError(InputError):
    pass


def require(value, message, kind=CompatibilityError):
    if not value:
        raise kind(message)


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class ExistingJournalAlias:
    def __init__(self, bridge, legacy_root):
        self.bridge = bridge
        self.root = Path(legacy_root)
        self.base = self.root / "public-evidence" / "integration" / "composition-attempt1"
        self.request_path = self.base / "prepared" / "INVERSE-REQUEST.json"
        self.journal_path = self.root / "journal"
        self.checker_calls = 0
        self._authenticate()

    def _authenticate(self):
        self.bridge._authenticate()
        manifest = self.root / "FROZEN-LEGACY-INPUTS.json"
        require(not manifest.is_symlink() and file_sha(manifest) == LEGACY_MANIFEST_SHA,
                "legacy input manifest changed", InputError)
        rows = json.loads(manifest.read_text())
        for row in rows:
            path = self.root / row["path"]
            require(not path.is_symlink() and path.stat().st_size == row["bytes"]
                    and file_sha(path) == row["sha256"], "legacy input changed", InputError)
        expected = {Path(row["path"]).name for row in rows if row["path"].startswith("journal/")}
        require(not self.journal_path.is_symlink() and len(expected) == 24
                and {p.name for p in self.journal_path.glob("state-*.json")} == expected,
                "legacy complete journal membership changed", InputError)

    def assert_compatible(self, prepared):
        """Pure identity/semantic guards; no numerical checker call."""
        self._authenticate()
        require(self.bridge.prepare(prepared.history) == prepared and prepared.request is not None,
                "prepared typed history changed")
        old = self.bridge.engine.read_request(self.request_path, OLD_REQUEST_SHA)
        raw = self.bridge.engine.read_json(self.request_path, OLD_REQUEST_SHA)
        current = prepared.request
        require(raw["model"] == current["model"] == MODEL
                and raw["quantity"] == current["quantity"] == QUANTITY
                and raw["schema"] == current["schema"] == self.bridge.engine.SCHEMA,
                "model/schema/shifted-unit mismatch")
        require(prepared.history["observation_map"] == MAP, "observation map mismatch")
        new_features = self.bridge._intervals(current["features"])
        require(all(old["observed"][k] == new_features[k] for k in FEATURES), "feature interval mismatch")
        for key in PHYSICAL:
            require((old["physical"][key].lo, old["physical"][key].hi) ==
                    tuple(self.bridge.core.rational(v) for v in DOMAIN[key]), "original domain mismatch")
            require(old["targets"][key] == self.bridge.core.rational(current["normalized_width_targets"][key]),
                    "normalized target mismatch")
        require(raw["budget"] == current["budget"], "original budget must remain unchanged")
        pins = self.bridge.engine.read_json(self.base / "CHECKER-PINS.json")
        current_pins = self.bridge.engine.source_pins()
        current_pins["global_check.py"] = file_sha(self.bridge.engine.BASE / "global_check.py")
        require(pins == current_pins, "numerical source identity mismatch", InputError)
        source_record = self.bridge.engine.read_json(self.root / "public-evidence" / "integration" / "SOURCE-PINS.json")
        require(source_record["sources"]["integration_core.py"] == CORE_SHA,
                "literal feature-map source mismatch", InputError)
        composed_path = self.base / "COMPOSED-RESULT.json"
        require(file_sha(composed_path) == OLD_COMPOSED_SHA, "composed identity changed", InputError)
        composed = self.bridge.engine.read_json(composed_path, OLD_COMPOSED_SHA)
        require(composed["inverse_request_sha256"] == OLD_REQUEST_SHA, "old composition request identity", InputError)
        require(source_record["admission_registry_sha256"] == composed["trusted_registry_sha256"]
                == self.bridge.core.TRUSTED_REGISTRY_SHA
                and source_record["provider_manifest_sha256"] == self.bridge.core.PROVIDER_MANIFEST_SHA,
                "old admission/provider registry identity", InputError)
        provenance = raw["provenance"]
        require(provenance["kind"] == "phased_count_confidence_composition"
                and provenance["scientific_premises_are_external"] is True, "old observation provenance", InputError)
        for key in ("admission_sha256", "analysis_request_sha256", "confidence_sha256", "dataset_sha256", "extraction_sha256"):
            require(provenance[key] == composed[key], "old provenance/composition mismatch", InputError)
        history = prepared.history
        require(history["mode"] == "cumulative" and len(history["blocks"]) == 1
                and len(prepared.selected_ids) == 1, "one existing cumulative event required")
        require(history["source_instance"] == provenance["dataset_sha256"]
                and prepared.selected_ids == (provenance["confidence_sha256"],), "old event alias mismatch")
        delta = self.bridge.core.rational(provenance["delta"])
        require(delta == self.bridge.core.rational(composed["delta"]) == self.bridge.core.rational("1/10"),
                "old delta provenance", InputError)
        require(delta == self.bridge.core.rational(prepared.error_allowance)
                == self.bridge.core.rational(history["error_budget"]), "delta mismatch")
        require(composed["admission_classification"] == "synthetic_model_check"
                and composed["confidence_error_bound_scope"] == "conditional_ideal_model_only"
                and composed["finite_generator_law_certified"] is False
                and composed["data_confidence_certificate_eligible"] is False
                and composed["data_confidence_certificate_issued"] is False,
                "original scientific scope changed", InputError)
        require(composed["scientific_premises"] == dict.fromkeys(("A1", "A2", "A3", "A4", "A5", "A6"),
                "ideal_model_semantics_reviewed_finite_rng_not_certified"), "original premises changed", InputError)
        return old, raw, composed, {k: v for k, v in pins.items() if k != "global_check.py"}

    def replay_equivalent(self, prepared):
        old, raw, composed, pins = self.assert_compatible(prepared)
        self.checker_calls += 1
        result = self.bridge.checker.recover(self.request_path, OLD_REQUEST_SHA, self.journal_path, pins, normal=True)
        self._authenticate()
        require(result.get("mode") == "normal_validated"
                and result.get("details", {}).get("complete_numeric_replay") is True,
                "legacy replay incomplete or invalid", InputError)
        expected = self.bridge.engine.read_json(self.base / "checker.stdout", composed["checker_output_sha256"])
        require(result == expected, "legacy mathematical replay differs", InputError)
        geometry = self.bridge.geometry_only(old, [entry["box"] for entry in result["physical_cover"]])
        require(geometry["widths"] == result["widths"], "complete union geometry mismatch", InputError)
        return {"schema": "typed_existing_journal_exact_alias_v1",
                "status": "LEGACY_SYNTHETIC_MODEL_CHECK_UNKNOWN_OUTER_COVER",
                "validated_legacy_request_sha256": OLD_REQUEST_SHA,
                "prepared_request_sha256": prepared.request_sha256,
                "prepared_history_sha256": digest(prepared.history),
                "constraint_relation": "exact_equal_model_map_domain_shifted_box_and_targets",
                "new_request_claimed_as_replayed": False, "old_request_or_journal_reserialized": False,
                "old_source_commit": OLD_COMMIT, "legacy_provenance": raw["provenance"],
                "legacy_admission_classification": composed["admission_classification"],
                "legacy_composed_status": composed["status"],
                "legacy_trusted_registry_sha256": composed["trusted_registry_sha256"],
                "legacy_scientific_premises": composed["scientific_premises"],
                "legacy_confidence_scope": composed["confidence_error_bound_scope"],
                "legacy_confidence_construction": composed["confidence_construction"],
                "legacy_confidence_error_upper_bound": composed["confidence_error_upper_bound"],
                "legacy_delta": composed["delta"], "new_statistical_events": 0,
                "original_data_reused_as_one_event": True,
                "finite_generator_law_certified": False, "scientific_admission_reverified": False,
                "data_confidence_certificate_eligible": False,
                "data_confidence_certificate_issued": False,
                "source_feasibility_certified": False, "parameter_accuracy_released": False,
                "checker_calls": self.checker_calls, "checker_result": result, "geometry": geometry}
