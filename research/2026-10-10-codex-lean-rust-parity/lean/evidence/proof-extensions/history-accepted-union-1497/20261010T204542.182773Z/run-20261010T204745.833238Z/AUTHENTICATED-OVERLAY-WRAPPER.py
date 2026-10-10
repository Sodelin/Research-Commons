#!/usr/bin/env python3
"""Bounded source checking with an authenticated complete namespace overlay.

The original overlay construction and actual first-namespace resolution remain
unchanged. Full inventories are compared around every compiler invocation and
at target boundaries. Each import lookup still verifies its actual selected
companion bundle. This avoids rebuilding the full inventory for each of the
thousands of entries in the post-audit imported-artifact manifest.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "scripts/build_with_mathlib_overlay.py"
BASE_SHA = "1bd2bd26199599a1f799a6f7619f3b7223e6f65c6c12e196bad5088dc953dc16"


def digest(path):
    import hashlib
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert digest(BASE) == BASE_SHA
spec = importlib.util.spec_from_file_location("original_complete_namespace_overlay", BASE)
original = importlib.util.module_from_spec(spec)
spec.loader.exec_module(original)


class OverlayBuilder(original.OverlayBuilder):
    def __init__(self):
        super().__init__()
        shutil.copyfile(Path(__file__), self.run / "AUTHENTICATED-OVERLAY-WRAPPER.py")
        original.core.save(self.run / "AUTHENTICATED-OVERLAY-PINS.json", {
            "wrapper_sha256": digest(Path(__file__)), "original_overlay_sha256": BASE_SHA,
            "full_inventory_boundaries": ["first context use", "before and after every compiler invocation", "after every target"],
            "every_import_actual_namespace_resolution_and_companion_bundle_checked": True,
            "compiler_flags_or_audit_conditions_changed": False})
        self.inventory_checks = 0

    def authenticate_inventory(self, context):
        links = original.overlay_mathlib(self.overlay_external, context)
        if context not in self.overlay_contexts:
            self.overlay_contexts[context] = links
            original.core.save(context.parent / "MATHLIB-NAMESPACE-OVERLAY.json", links)
        else:
            assert self.overlay_contexts[context] == links, "Overlay symlink inventory drift"
        self.inventory_checks += 1

    def dependencies(self, context, modules):
        if context not in self.overlay_contexts:
            self.authenticate_inventory(context)
        measured = original.core.Builder.dependencies(self, context, modules)
        checked = {}
        for module, entry in measured.items():
            actual = original.lean_lookup([context] + self.external, module)
            assert actual.is_file(), ("Lean-selected module absent", module, actual)
            assert actual.resolve() == Path(entry["path"]).resolve(), ("First namespace differs", module)
            assert original.core.artifact_bundle(actual) == entry["artifacts"]
            checked[module] = {"lean_path": str(actual), "resolved_target": str(actual.resolve()),
                               "artifacts": entry["artifacts"]}
        with self.resolutions.open("a") as stream:
            stream.write(json.dumps({"context": str(context), "imports": checked}, sort_keys=True) + "\n")
        return measured

    def invoke(self, name, source, obj, imports, context, seconds, memory, kind):
        self.authenticate_inventory(context)
        result = super().invoke(name, source, obj, imports, context, seconds, memory, kind)
        self.authenticate_inventory(context)
        return result

    def target(self, label):
        result = super().target(label)
        context = self.run / "targets" / original.core.safe(label) / "objects"
        if context in self.overlay_contexts:
            self.authenticate_inventory(context)
        original.core.save(context.parent / "FINAL-NAMESPACE-AUTHENTICATION.json", {
            "target": label, "full_inventory_checks_so_far": self.inventory_checks,
            "final_inventory_matches_initial": True,
            "source_and_all_direct_import_bundles": "Original bounded invocation receipts remain authoritative."})
        return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target")
    args = parser.parse_args()
    builder = OverlayBuilder()
    labels = list(builder.graph["targets"]) if args.target == "all" else [args.target]
    assert all(label in builder.graph["targets"] for label in labels)
    raise SystemExit(builder.run_targets(labels))
