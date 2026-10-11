#!/usr/bin/env python3
"""Run one reviewed storage derivative over a strict authenticated proof target."""
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
    optimized = prep.get("optimized_overlay_sha256")
    filename = "build_with_authenticated_overlay.py" if optimized else "build_with_mathlib_overlay.py" if overlay else "build_connected.py"
    if overlay:
        assert sha(workspace / "scripts/build_with_mathlib_overlay.py") == prep["namespace_overlay_wrapper_sha256"]
        if optimized:
            assert sha(workspace / "scripts" / filename) == optimized
    spec = importlib.util.spec_from_file_location("frozen_proof_extension_builder", workspace / "scripts" / filename)
    builder_module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder_module)
    assert overlay and optimized, 'Storage derivative requires authenticated namespace parent'
    adapter_path = workspace / 'scripts/storage_wrapper.py'
    policy_path = workspace / 'STDERR-STORAGE-POLICY.json'
    assert sha(adapter_path) == prep['storage_wrapper_sha256']
    assert sha(policy_path) == prep['storage_policy_sha256']
    policy = json.loads(policy_path.read_bytes())
    assert policy['runtime_authorized'] is True
    adapter_spec = importlib.util.spec_from_file_location('frozen_compressed_stderr_adapter', adapter_path)
    adapter_module = importlib.util.module_from_spec(adapter_spec)
    adapter_spec.loader.exec_module(adapter_module)
    # Bind the SAME core module object already used by the two parent classes.
    builder_class = adapter_module.make_builder_class(
        builder_module.OverlayBuilder, builder_module.original.core, policy)
    builder = builder_class()
    shutil.copyfile(adapter_path, builder.run / 'COMPRESSED-STDERR-STORAGE-WRAPPER.py')
    shutil.copyfile(policy_path, builder.run / 'STDERR-STORAGE-POLICY.json')
    save(builder.run / 'COMPRESSED-STDERR-STORAGE-PINS.json', {
        'adapter_sha256':sha(adapter_path),'policy_sha256':sha(policy_path),
        'canonical_core_sha256':sha(workspace / 'scripts/build_connected.py'),
        'authenticated_parent_sha256':optimized,
        'namespace_parent_sha256':prep['namespace_overlay_wrapper_sha256'],
        'same_core_module_object':True,
        'qualification':'LD_DEBUG libs combined stderr gzip; stronger initialized-native presence; fresh same-FS immutable aliases. Strict compiler/kernel/import/audit policies retained.'})
    targets = args.target or list(builder.graph["targets"])
    assert len(targets) == len(set(targets)) and all(t in builder.graph["targets"] for t in targets)
    shutil.copyfile(Path(__file__), builder.run / "MULTI-TARGET-LAUNCHER.py")
    save(builder.run / "MULTI-TARGET-LAUNCHER-PINS.json", {
        "launcher_sha256": sha(Path(__file__)), "preparation_sha256": sha(workspace / "PREPARATION.json"),
        "targets": targets, "policy": "Serial invocation of the strict frozen core through a reviewed logging/cache storage derivative; no compiler/kernel/import/audit/cap override."})
    raise SystemExit(builder.run_targets(targets))


if __name__ == "__main__":
    main()
