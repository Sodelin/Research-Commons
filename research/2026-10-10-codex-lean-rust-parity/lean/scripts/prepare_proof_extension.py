#!/usr/bin/env python3
"""Freeze new proof roots over explicit exact-version original contexts.

Context composition compares module, source hash and literal imports. Replacing
an original module requires --replace-existing and records both original and
derivative identities. No prior target or audit status is carried forward.
"""
from __future__ import annotations
import argparse
import datetime
import json
from pathlib import Path
import re
import shutil
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]
OVERLAY = ROOT / ".build/recovery/coefficients/20261010T111018.094654Z/scripts/build_with_mathlib_overlay.py"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--context", nargs=2, action="append", required=True,
                        metavar=("WORKSPACE", "TARGET"))
    parser.add_argument("--source", type=Path, action="append", required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--replace-existing", action="store_true")
    parser.add_argument("--include-context-roots", action="store_true")
    parser.add_argument("--separate-roots", action="store_true")
    parser.add_argument("--optimized-overlay", action="store_true")
    args = parser.parse_args()
    assert re.fullmatch(r"[A-Za-z0-9_/-]+", args.label)
    assert not args.label.startswith("/") and ".." not in args.label
    entries, source_paths, contexts, inherited_roots = {}, {}, [], []
    for workspace, target in args.context:
        work = Path(workspace).resolve()
        graph_path = work / "DEPENDENCY-GRAPH.json"
        graph = json.loads(graph_path.read_bytes())
        selected = graph["targets"][target]
        contexts.append({"workspace": str(work), "target": target,
                         "graph_sha256": sha(graph_path), "selected_modules": len(selected["order"])})
        inherited_roots.extend(selected["roots"])
        for module in selected["order"]:
            row = selected["modules"][module]
            source = work / "source-store" / (row["sha256"] + ".lean")
            assert sha(source) == row["sha256"]
            if module in entries:
                prior = entries[module]
                assert (prior["sha256"], prior["imports"]) == (row["sha256"], row["imports"]), (
                    "Incompatible exact original module contexts", module)
            else:
                entries[module] = row
                source_paths[module] = source
    derivatives, new_roots = [], []
    for source in args.source:
        source = source.resolve()
        module = source.stem
        assert re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", module)
        row = {"module": module, "sha256": sha(source),
               "imports": re.findall(r"^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)", source.read_text(), re.M)}
        previous = entries.get(module)
        if previous:
            assert args.replace_existing
            assert previous["imports"] == row["imports"], ("Replacement changes imports", module)
        derivatives.append({"module": module, "source": str(source), "source_sha256": row["sha256"],
                            "replaces_original_sha256": previous["sha256"] if previous else None})
        entries[module], source_paths[module] = row, source
        new_roots.append(module)
    roots = list(dict.fromkeys((inherited_roots if args.include_context_roots else []) + new_roots))

    def closure(roots):
        order, seen, active = [], set(), set()
        def visit(module):
            if module in seen:
                return
            assert module not in active, ("Import cycle", module)
            active.add(module)
            for dependency in entries[module]["imports"]:
                if dependency in entries:
                    visit(dependency)
                else:
                    assert dependency in {"Init", "Std", "Lean", "Mathlib"} or dependency.startswith(
                        ("Init.", "Std.", "Lean.", "Mathlib.")), ("Missing project dependency", module, dependency)
            active.remove(module)
            seen.add(module)
            order.append(module)
        for module in roots:
            visit(module)
        return order

    targets = {}
    groups = [(args.label + "/" + m, [m]) for m in roots] if args.separate_roots else [(args.label, roots)]
    for label, selected_roots in groups:
        order = closure(selected_roots)
        targets[label] = {"roots": selected_roots, "order": order,
                          "modules": {m: entries[m] for m in order},
                          "required_for_accepted_release": False, "status": "UNCOMPILED_EXACT_PROOF_EXTENSION"}
    all_selected = set(m for target in targets.values() for m in target["order"])
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    name = args.label.replace("/", "_")
    work = ROOT / ".build/proof-extensions" / name / stamp
    evidence = ROOT / "evidence/proof-extensions" / name / stamp
    (work / "source-store").mkdir(parents=True)
    for module in sorted(all_selected):
        source = source_paths[module]
        assert sha(source) == entries[module]["sha256"]
        shutil.copyfile(source, work / "source-store" / (sha(source) + ".lean"))
        frozen = evidence / "sources" / (module.replace(".", "/") + ".lean")
        frozen.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, frozen)
    graph = {"targets": targets, "scope": {
        "status": "New exact proof contexts pending fresh kernel and complete owned audit",
        "contexts": contexts, "derivatives": derivatives, "historical_contexts_unchanged": True}}
    save(work / "DEPENDENCY-GRAPH.json", graph)
    save(evidence / "DEPENDENCY-GRAPH.json", graph)
    (work / "scripts").mkdir()
    for name in ["build_connected.py", "AuditTemplate.lean"]:
        shutil.copyfile(ROOT / "scripts" / name, work / "scripts" / name)
    use_overlay = "Mathlib.Data.FinEnum" in all_selected
    if use_overlay:
        shutil.copyfile(OVERLAY, work / "scripts/build_with_mathlib_overlay.py")
        assert "CORE_SHA = '" + sha(work / "scripts/build_connected.py") + "'" in OVERLAY.read_text()
        if args.optimized_overlay:
            shutil.copyfile(ROOT / "scripts/build_with_authenticated_overlay.py", work / "scripts/build_with_authenticated_overlay.py")
    license_source = Path("/workspace/dependencies/mathlib4/LICENSE")
    (work / "third-party/mathlib").mkdir(parents=True)
    shutil.copyfile(license_source, work / "third-party/mathlib/LICENSE")
    preparation = {"status": "PREPARED_UNCOMPILED_EXACT_PROOF_EXTENSION", "workspace": str(work),
        "evidence": str(evidence), "targets": {k: len(t["order"]) for k, t in targets.items()},
        "graph_sha256": sha(work / "DEPENDENCY-GRAPH.json"), "contexts": contexts,
        "derivatives": derivatives, "source_versions_and_literal_imports_pinned": True,
        "builder_sha256": sha(work / "scripts/build_connected.py"),
        "audit_template_sha256": sha(work / "scripts/AuditTemplate.lean"),
        "official_complete_mathlib_namespace_overlay": use_overlay,
        "namespace_overlay_wrapper_sha256": sha(work / "scripts/build_with_mathlib_overlay.py") if use_overlay else None,
        "optimized_overlay_sha256": sha(work / "scripts/build_with_authenticated_overlay.py") if use_overlay and args.optimized_overlay else None,
        "source_pins": {m: entries[m]["sha256"] for m in sorted(all_selected)},
        "historical_passes_copied": False, "native_execution_claimed": False}
    save(work / "PREPARATION.json", preparation)
    save(evidence / "PREPARATION.json", preparation)
    save(ROOT / (args.label.replace("/", "_").upper() + "-PREPARATION.json"), preparation)
    print(json.dumps({k: preparation[k] for k in ["status", "workspace", "targets"]}))


if __name__ == "__main__":
    main()
