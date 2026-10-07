"""Fixed-model constraint preparation and existing-checker bridge; no sampler.

All outputs remain unadmitted/conditional geometry. This module does not infer
scientific premises from a caller's flags or reimplement numerical contractors.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import importlib
import importlib.util
import json
import re
import sys

from genealogy_workbench.core import InputError
from genealogy_workbench.provenance import canonical, digest

MODEL = "fixed-six-copy-clock-jc-nine-v1"
MAP = "complete-six-copy-two-site-character-vector-v1"
QUANTITY = "shifted_bernoulli_character_mean"
FEATURES = ("AC1", "AC2", "CC1", "BC1", "BC2", "AB1", "AB2", "AA1", "BB1")
PHYSICAL = ("h", "u", "v", "rA", "rB", "rC", "rAB", "rR", "g")
DOMAIN = {k: ["1/32", "1/8"] if k in ("h", "u", "v") else
          ["1/6", "2/3"] if k == "g" else ["1/2", "6"] for k in PHYSICAL}
CORE_SHA = "f409f3ae1cfeb04db61f7b3b9f0aad76e18e372c57289463ad7d5622023b131e"
PROFILE = "msci-ab-profile-implementation-20261005-1612z"
BACKEND_PINS_SHA = "4ad618a856bebd4624e032bd0d0db0e8208a521b58172e3d011d237c3205afad"


def require(test, reason):
    if not test:
        raise InputError(reason)


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


@dataclass(frozen=True)
class Prepared:
    """Immutable bytes, not a numerical or scientific acceptance token."""
    history_json: bytes
    request_json: bytes | None
    status: str
    selected_ids: tuple
    error_allowance: str

    @property
    def history(self):
        return json.loads(self.history_json)

    @property
    def request(self):
        return None if self.request_json is None else json.loads(self.request_json)

    @property
    def request_sha256(self):
        return None if self.request_json is None else hashlib.sha256(self.request_json).hexdigest()


class FixedJCBridge:
    def __init__(self, runtime_root, integration_core_path):
        root = Path(runtime_root).resolve()
        pin_path = Path(__file__).with_name("BACKEND-PINS.json")
        require(file_sha(pin_path) == BACKEND_PINS_SHA, "backend pin manifest changed")
        self._pins = json.loads(pin_path.read_text())
        for relative, expected in self._pins.items():
            path = root / relative
            require(not path.is_symlink() and file_sha(path) == expected, "backend source changed")
        core_path = Path(integration_core_path).resolve()
        require(file_sha(core_path) == CORE_SHA, "literal extractor source changed")
        self._root, self._core_path = root, core_path
        folder = root / PROFILE
        for name in ("interval_math", "base_contractors", "interval_ad", "joint_contractor",
                     "global_contractors", "global_engine", "global_check"):
            if name in sys.modules:
                require(Path(sys.modules[name].__file__).resolve() == folder / (name + ".py"),
                        "conflicting backend import")
        sys.path.insert(0, str(folder))
        self.engine = importlib.import_module("global_engine")
        self.checker = importlib.import_module("global_check")
        spec = importlib.util.spec_from_file_location("_typed_jc_literal_core", core_path)
        self.core = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.core)
        require(self.engine.MODEL == MODEL and tuple(self.engine.ops.FEATURES) == FEATURES
                and tuple(self.engine.ops.PHYSICAL) == PHYSICAL, "backend interface mismatch")

    def _authenticate(self):
        for relative, expected in self._pins.items():
            path = self._root / relative
            require(not path.is_symlink() and file_sha(path) == expected, "backend source changed")
        require(file_sha(self._core_path) == CORE_SHA, "literal extractor source changed")

    def extract(self, data, expected_loci, selection_sha256):
        """Reuse literal complete-panel extraction; this does not admit the data."""
        self._authenticate()
        require(type(expected_loci) is int and 1 <= expected_loci <= self.core.MAX_LOCI,
                "literal extraction locus cap")
        result = self.core.extract(data, expected_loci, selection_sha256)
        self._authenticate()
        return result

    def _intervals(self, row):
        self.core.exact_keys(row, FEATURES, "shifted mean box")
        out = {}
        for name in FEATURES:
            pair = row[name]
            require(isinstance(pair, list) and len(pair) == 2, "two exact endpoints required")
            lo, hi = (self.core.rational(x) for x in pair)
            require(0 <= lo <= hi <= 1, "shifted endpoint range")
            out[name] = self.engine.m.I(lo, hi)
        return out

    def prepare(self, history):
        """Prepare same-map constraints; never issue a data-confidence certificate."""
        self._authenticate()
        self.core.exact_keys(history, ("schema", "model", "observation_map", "quantity",
            "source_instance", "domain", "mode", "confidence_mode", "error_budget", "blocks", "inverse_budget"), "history")
        require(history["schema"] == "fixed-jc-constraint-history-v1" and history["model"] == MODEL,
                "fixed model required")
        require(history["observation_map"] == MAP and history["quantity"] == QUANTITY,
                "fixed shifted observation map required")
        source = history["source_instance"]
        require(isinstance(source, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,64}", source), "source identity")
        self.core.exact_keys(history["domain"], PHYSICAL, "original domain")
        for name in PHYSICAL:
            pair = history["domain"][name]
            require(isinstance(pair, list) and len(pair) == 2, "domain interval")
            require(tuple(self.core.rational(x) for x in pair) == tuple(Q(x) for x in DOMAIN[name]),
                    "original full domain must be preserved")
        require(history["mode"] in ("fresh_only", "cumulative"), "declared update mode")
        require(history["confidence_mode"] == "preallocated_fixed_blocks",
                "fixed-block mode only; no inherited anytime claim")
        budget = self.core.rational(history["error_budget"])
        require(0 < budget < 1, "error budget outside (0,1)")
        blocks = history["blocks"]
        require(isinstance(blocks, list) and 1 <= len(blocks) <= 32, "bounded nonempty history")
        parsed, ids = [], set()
        for block in blocks:
            self.core.exact_keys(block, ("id", "source_instance", "observation_map", "quantity",
                "evidence_kind", "error_allowance", "shifted_mean_box"), "constraint block")
            name = block["id"]
            require(isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,64}", name)
                    and name not in ids, "unique constraint block identity")
            ids.add(name)
            require(block["source_instance"] == source and block["observation_map"] == MAP
                    and block["quantity"] == QUANTITY, "one source and fixed shifted map required")
            require(block["evidence_kind"] == "conditional_constraints_not_admitted",
                    "exact-law/catalogue/admission flags are not accepted here")
            allowance = self.core.rational(block["error_allowance"])
            require(0 < allowance < 1, "block error allowance")
            parsed.append((name, allowance, self._intervals(block["shifted_mean_box"])))
        selected = parsed[-1:] if history["mode"] == "fresh_only" else parsed
        used = sum((v[1] for v in selected), Q(0))
        require(used <= budget, "insufficient error budget")
        stored = canonical(history)
        names = tuple(v[0] for v in selected)
        observed = dict(selected[0][2])
        try:
            for _, _, row in selected[1:]:
                observed = {key: self.engine.m.meet(observed[key], row[key]) for key in FEATURES}
        except self.engine.m.Inconsistent:
            return Prepared(stored, None, "CONSTRAINT_INTERSECTION_EMPTY", names, str(used))
        try:
            for value in observed.values():
                self.engine.m.meet(value * 2 - 1, self.engine.m.I(0, 1))
        except self.engine.m.Inconsistent:
            return Prepared(stored, None, "MODEL_RAW_RANGE_EMPTY", names, str(used))
        request = {"schema": self.engine.SCHEMA, "model": MODEL, "quantity": QUANTITY,
            "box": DOMAIN, "features": {k: [str(v.lo), str(v.hi)] for k, v in observed.items()},
            "normalized_width_targets": dict.fromkeys(PHYSICAL, "1/20"),
            "budget": history["inverse_budget"],
            "provenance": {"kind": "unadmitted_fixed_map_constraint_history",
                "history_sha256": digest(history), "source_instance": source,
                "retained_block_ids": list(names), "mode": history["mode"],
                "conditional_error_allowance": str(used), "scientific_premises_are_external": True,
                "data_confidence_certificate_issued": False}}
        return Prepared(stored, self.engine.canonical(request), "REQUEST_PREPARED_NOT_ADMITTED", names, str(used))

    def write_request(self, prepared, path):
        require(prepared.request_json is not None, "empty constraints have no numerical request")
        with Path(path).open("xb") as out:
            out.write(prepared.request_json)
        return self.read_prepared(prepared, path)

    def read_prepared(self, prepared, path):
        self._authenticate()
        rebuilt = self.prepare(prepared.history)
        require(rebuilt == prepared and prepared.request_json is not None, "prepared record changed")
        return self.engine.read_request(path, prepared.request_sha256)

    def geometry_only(self, parsed_request, boxes):
        """Reuses the complete-union goal function; does NOT validate a journal."""
        require(isinstance(boxes, list), "complete cover list required")
        frontier = {}
        for index, box in enumerate(boxes):
            self.core.exact_keys(box, PHYSICAL, "complete physical box")
            physical = {}
            for name, pair in box.items():
                require(isinstance(pair, list) and len(pair) == 2, "physical endpoints")
                lo, hi = (self.core.rational(x) for x in pair)
                dom = parsed_request["physical"][name]
                require(dom.lo <= lo <= hi <= dom.hi, "cover outside original domain")
                physical[name] = self.engine.m.I(lo, hi)
            frontier[str(index)] = {"state": {"physical": physical}}
        met, widths = self.engine.goal(parsed_request, frontier)
        return {"nonempty": bool(boxes), "whole_union_width_target_met": met, "widths": widths,
                "numeric_journal_validated": False, "data_confidence_certificate_issued": False}

    def replay(self, prepared, request_path, journal_path):
        """Invoke the existing checker, never accept a caller-provided PASS JSON."""
        request = self.read_prepared(prepared, request_path)
        result = self.checker.recover(request_path, prepared.request_sha256, journal_path,
                                     self.engine.source_pins(), normal=True)
        self._authenticate()
        mode = result.get("mode")
        require(mode in ("normal_validated", "recovered_same_process_validated_prefix",
                         "recovered_authenticated_original_domain"), "unknown checker mode")
        require(result.get("request_sha256") == prepared.request_sha256
                and result.get("model") == MODEL, "checker request/model identity")
        geometry = self.geometry_only(request, [v["box"] for v in result["physical_cover"]])
        require(geometry["widths"] == result["widths"], "complete checker union widths")
        normal = mode == "normal_validated" and result.get("details", {}).get("complete_numeric_replay") is True
        status = ("UNADMITTED_CONDITIONAL_CONFLICT" if normal and not geometry["nonempty"] else
                  "UNADMITTED_CONDITIONAL_GEOMETRY_WIDTH_MET" if normal and geometry["whole_union_width_target_met"]
                  else "UNKNOWN_OUTER_COVER")
        return {"status": status, "history_sha256": digest(prepared.history),
                "validated_request_sha256": prepared.request_sha256, "checker_mode": mode,
                "conditional_error_allowance": prepared.error_allowance, "checker_invoked": True,
                "checker_result": result, "geometry": geometry,
                "scientific_admission_verified": False, "data_confidence_certificate_issued": False}

    def stale_replay(self, old, new, old_request_path, old_journal_path):
        """Validate the OLD journal and label its nested-use provenance unchanged."""
        require(new.history["mode"] == "cumulative", "no automatic fresh-only nesting")
        require(old.request is not None and new.request is not None, "nonempty request pair required")
        require(old.history["source_instance"] == new.history["source_instance"], "stale source mismatch")
        require(self.prepare(new.history) == new, "new prepared record changed")
        a, b = old.request["features"], new.request["features"]
        require(all(Q(a[k][0]) <= Q(b[k][0]) <= Q(b[k][1]) <= Q(a[k][1]) for k in FEATURES),
                "new constraint box is not contained in old box")
        checked = self.replay(old, old_request_path, old_journal_path)
        return {**checked, "status": "STALE_UNKNOWN_OUTER_COVER", "new_request_sha256": new.request_sha256,
                "new_history_sha256": digest(new.history), "stale_history_sha256": checked["history_sha256"],
                "conditional_error_allowance": new.error_allowance,
                "new_data_numerically_processed": False, "old_journal_relabelled": False}
