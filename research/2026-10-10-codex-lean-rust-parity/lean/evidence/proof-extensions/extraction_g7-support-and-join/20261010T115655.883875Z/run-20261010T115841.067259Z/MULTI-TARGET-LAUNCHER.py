#!/usr/bin/env python3
"""Run the frozen bounded builder over separate new proof targets serially."""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
from check_core import save, sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("--target", action="append")
    args = parser.parse_args()
    workspace = args.workspace.resolve()
    prep = json.loads((workspace / "PREPARATION.json").read_bytes())
    assert sha(workspace / "DEPENDENCY-GRAPH.json") == prep["graph_sha256"]
    assert sha(workspace / "scripts/build_connected.py") == prep["builder_sha256"]
    assert sha(workspace / "scripts/AuditTemplate.lean") == prep["audit_template_sha256"]
    overlay = prep["official_complete_mathlib_namespace_overlay"]
    filename = "build_with_mathlib_overlay.py" if overlay else "build_connected.py"
    if overlay:
        assert sha(workspace / "scripts" / filename) == prep["namespace_overlay_wrapper_sha256"]
    spec = importlib.util.spec_from_file_location("frozen_proof_extension_builder", workspace / "scripts" / filename)
    builder_module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder_module)
    builder = (builder_module.OverlayBuilder if overlay else builder_module.Builder)()
    targets = args.target or list(builder.graph["targets"])
    assert len(targets) == len(set(targets)) and all(t in builder.graph["targets"] for t in targets)
    shutil.copyfile(Path(__file__), builder.run / "MULTI-TARGET-LAUNCHER.py")
    save(builder.run / "MULTI-TARGET-LAUNCHER-PINS.json", {
        "launcher_sha256": sha(Path(__file__)), "preparation_sha256": sha(workspace / "PREPARATION.json"),
        "targets": targets, "policy": "Serial invocation of the frozen unchanged builder; no compiler/audit/cap override."})
    raise SystemExit(builder.run_targets(targets))


if __name__ == "__main__":
    main()
