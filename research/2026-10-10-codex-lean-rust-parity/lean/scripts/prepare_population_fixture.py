#!/usr/bin/env python3
"""Freeze the actual original population fixture and exact compatible imports.

The admitted two-tip source/typed bank and original effective coefficients are
combined by module, source hash and literal import list. New support and fixture
roots are uncompiled until their own bounded kernel invocation and owned audit.
No broad imports, executable providers or historical context are substituted.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import shutil
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]
NEW = ["G7EffectiveCoefficientSupport", "G7EncodedMergerSupport", "G7OriginalPopulationFixture"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coefficients_workspace", type=Path)
    args = parser.parse_args()
    coeff = args.coefficients_workspace.resolve()
    cert = json.loads((ROOT / "COEFFICIENT-RECOVERY-CERTIFICATE.json").read_bytes())
    assert Path(cert["workspace"]) == coeff
    assert cert["targets"]["candidate/g7-coefficients"]["status"] == "PASS"
    typed = json.loads((ROOT / "TYPED-REUSE-CERTIFICATE.json").read_bytes())
    assert typed["status"] == "PASS_ORIGINAL_BANK_AND_NATIVE_TWO_TIP_COMPILER_FIXTURES"
    graphs = json.loads((coeff / "DEPENDENCY-GRAPH.json").read_bytes())
    current = json.loads((ROOT / "DEPENDENCY-GRAPH.json").read_bytes())["targets"]["current/connected"]
    entries = dict(graphs["targets"]["candidate/g7-coefficients"]["modules"])
    source_paths = {m: coeff / "source-store" / (r["sha256"] + ".lean") for m, r in entries.items()}
    typed_evidence = ROOT / typed["evidence"]
    for provider in typed["provider_records"]:
        m = provider["module"]
        row = current["modules"][m]
        assert row["sha256"] == provider["source_sha256"]
        if m in entries:
            assert entries[m] == row, ("Incompatible original provider", m)
        else:
            entries[m] = row
            source_paths[m] = typed_evidence / "providers" / (m.replace(".", "/") + ".lean")
    for record in typed["new_module_records"]:
        m = record["module"]
        source = typed_evidence / (m.replace(".", "/") + ".lean")
        assert sha(source) == record["source_sha256"]
        entries[m] = {"module": m, "sha256": sha(source),
                      "imports": re.findall(r"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", source.read_text(), re.M)}
        source_paths[m] = source
    for m in NEW:
        source = ROOT.parent / "reuse/sources" / (m + ".lean")
        entries[m] = {"module": m, "sha256": sha(source),
                      "imports": re.findall(r"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", source.read_text(), re.M)}
        source_paths[m] = source
    order = []
    seen = set()
    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for imported in entries[m]["imports"]:
            if imported in entries:
                visit(imported)
            else:
                assert imported in {"Mathlib", "Lean", "Std", "Init"} or imported.startswith(
                    ("Mathlib.", "Lean.", "Std.", "Init.")), ("Missing project import", m, imported)
        order.append(m)
    roots = NEW
    for m in roots:
        visit(m)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    work = ROOT / ".build/source-population" / stamp
    evidence = ROOT / "evidence/source-population" / stamp
    store = work / "source-store"
    store.mkdir(parents=True)
    for m in order:
        p = source_paths[m]
        assert sha(p) == entries[m]["sha256"]
        shutil.copy2(p, store / (sha(p) + ".lean"))
        frozen = evidence / "sources" / (m.replace(".", "/") + ".lean")
        frozen.parent.mkdir(parents=True, exist_ok=True)
        frozen.write_bytes(p.read_bytes())
    graph = {"targets": {"extraction/original-population-fixture": {
                "roots": roots, "order": order, "modules": {m: entries[m] for m in order},
                "required_for_accepted_release": False, "status": "UNCOMPILED_NEW_EXACT_CONTEXT"}},
             "scope": {"status": "Type-safe original population fixture; kernel checking and execution remain separate.",
                       "third_party_modules": ["Mathlib.Data.FinEnum"],
                       "code_universe_enumeration": False,
                       "whole_native_LAW_refinement_claimed": False}}
    save(work / "DEPENDENCY-GRAPH.json", graph)
    scripts = work / "scripts"
    scripts.mkdir()
    for name in ["build_connected.py", "AuditTemplate.lean", "build_with_mathlib_overlay.py"]:
        shutil.copy2(coeff / "scripts" / name, scripts / name)
    if (coeff / "third-party").is_dir():
        shutil.copytree(coeff / "third-party", work / "third-party")
    license_path = Path("/workspace/dependencies/mathlib4/LICENSE")
    (work / "third-party/mathlib").mkdir(parents=True, exist_ok=True)
    shutil.copy2(license_path, work / "third-party/mathlib/LICENSE")
    receipt = {"status": "PREPARED_UNCOMPILED_ORIGINAL_POPULATION_FIXTURE",
               "workspace": str(work), "evidence": str(evidence),
               "graph_sha256": sha(work / "DEPENDENCY-GRAPH.json"), "closure_modules": len(order),
               "coefficient_workspace": str(coeff), "coefficient_certificate_sha256": sha(ROOT / "COEFFICIENT-RECOVERY-CERTIFICATE.json"),
               "typed_certificate_sha256": sha(ROOT / "TYPED-REUSE-CERTIFICATE.json"),
               "source_pins": {m: entries[m]["sha256"] for m in order},
               "source_versions_or_imports_changed": False,
               "new_roots": NEW, "separate_native_execution_required": True,
               "third_party_mathlib_license_sha256": sha(license_path),
               "cache_reuse_must_be_authenticated_by_actual_import_bundles": True}
    save(work / "PREPARATION.json", receipt)
    save(evidence / "PREPARATION.json", receipt)
    save(evidence / "DEPENDENCY-GRAPH.json", graph)
    save(ROOT / "POPULATION-FIXTURE-PREPARATION.json", receipt)
    print(json.dumps({k: receipt[k] for k in ["status", "workspace", "closure_modules"]}))


if __name__ == "__main__":
    main()
