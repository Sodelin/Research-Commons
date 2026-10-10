#!/usr/bin/env python3
"""Freeze a storage-only installer over exact immutable staged cache bundles.

Contributor: Codex / lean_integration_successor, 2026-10-10.
The unchanged strict core still authenticates the original receipt.cached_object
and every cache key/import bundle. Only its overlay install method may use the
already verified same-byte local staged companion bundle for a hard link.
Original receipts, paths, keys, compiler flags, caps and audits remain unchanged.
This preparer accepts only a new, uncompiled, four-provider context.
"""
from __future__ import annotations

import argparse
import datetime
import json
from pathlib import Path
import shutil

from check_core import bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]
CORE_SHA = "13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc"
AUDIT_SHA = "f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a"
ORIGINAL_OVERLAY = "09b24ef22790f14e0fa7bc3ae6b0a9c2b1fe8d2d9cbfdfae5333b0dd566536c0"
ORIGINAL_AUTHENTICATED = "ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc"

INSTALL_METHOD = '''    def install(self, base, out, expected):
        """Verify original inputs, then hard-link an exact staged local alias."""
        import errno
        original_base = base
        assert core.artifact_bundle(original_base) == expected, ('Original companion drift', original_base)
        manifest_path = ROOT / 'CACHE-INSTALL-ALIASES.json'
        assert sha(manifest_path) == CACHE_INSTALL_MANIFEST_SHA, 'Install manifest drift'
        if not hasattr(self, 'cache_install_aliases'):
            manifest = core.read(manifest_path)
            assert manifest['workspace'] == str(ROOT) and manifest['graph_sha256'] == self.graph_sha
            self.cache_install_aliases = {entry['original_cached_object']: entry for entry in manifest['entries']}
            assert len(self.cache_install_aliases) == len(manifest['entries'])
            shutil.copyfile(manifest_path, self.run / 'CACHE-INSTALL-ALIASES.json')
            core.save(self.run / 'CACHE-INSTALL-TRANSPORT-PINS.json', {
                'manifest_sha256': CACHE_INSTALL_MANIFEST_SHA,
                'derivation_sha256': sha(ROOT / 'CACHE-INSTALL-TRANSPORT-DERIVATION.json'),
                'original_receipt_paths_and_bytes_unchanged': True,
                'original_and_staged_companions_verified_before_and_after_install': True,
                'core_builder_sha256': sha(core_path),
                'compiler_flags_caps_cache_keys_and_audit_unchanged': True})
        entry = self.cache_install_aliases.get(str(original_base))
        if entry is not None:
            assert entry['object_artifacts'] == expected
            receipt = Path(entry['original_receipt'])
            staged_receipt = Path(entry['staged_receipt'])
            assert sha(receipt) == sha(staged_receipt) == entry['receipt_sha256'], 'Receipt drift'
            rec = core.read(receipt)
            assert rec['cached_object'] == str(original_base) and rec['object_artifacts'] == expected
            base = Path(entry['staged_cached_object'])
            assert base.is_relative_to(self.cache) and base.parent.name == entry['cache_key']
            assert core.artifact_bundle(base) == expected, ('Staged companion drift', base)
        assert out.is_relative_to(self.run), ('Install destination outside fresh run', out)
        out.parent.mkdir(parents=True, exist_ok=True)
        transports = []
        for suffix in core.SUFFIXES:
            source, destination = core.companion(base, suffix), core.companion(out, suffix)
            if source.exists():
                assert sha(source) == expected[suffix]
                if destination.exists():
                    assert sha(destination) == sha(source), ('Existing context artifact differs', destination)
                    mode = 'VERIFIED_EXISTING_DESTINATION'
                else:
                    try:
                        os.link(source, destination)
                        mode = 'SAME_FILESYSTEM_HARD_LINK'
                        assert (source.stat().st_dev, source.stat().st_ino) == (destination.stat().st_dev, destination.stat().st_ino)
                    except OSError as error:
                        if error.errno != errno.EXDEV:
                            raise
                        shutil.copy2(source, destination)
                        mode = 'EXDEV_HASH_CHECKED_COPY2'
                assert sha(destination) == sha(source) == expected[suffix]
                transports.append({'suffix': suffix, 'source': str(source), 'destination': str(destination),
                    'sha256': expected[suffix], 'bytes': source.stat().st_size, 'transport': mode,
                    'source_device_inode': [source.stat().st_dev, source.stat().st_ino],
                    'destination_device_inode': [destination.stat().st_dev, destination.stat().st_ino]})
        assert core.artifact_bundle(original_base) == expected, ('Original changed during install', original_base)
        assert core.artifact_bundle(base) == expected, ('Staged changed during install', base)
        assert core.artifact_bundle(out) == expected, ('Installed companion drift', out)
        if entry is not None:
            assert sha(Path(entry['original_receipt'])) == sha(Path(entry['staged_receipt'])) == entry['receipt_sha256']
        with (self.run / 'CACHE-INSTALL-TRANSPORT-CHECKS.jsonl').open('a') as stream:
            stream.write(json.dumps({'original_object': str(original_base), 'install_source': str(base),
                'destination': str(out), 'cache_key': entry['cache_key'] if entry is not None else None,
                'object_artifacts': expected, 'original_and_staged_pre_post_checks_pass': True,
                'files': transports}, sort_keys=True) + '\\n')

'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("--selection-manifest", type=Path, required=True)
    args = parser.parse_args()
    work = args.workspace.resolve(strict=True)
    assert not (work / ".build/LATEST-RUN.json").exists(), "Only a new uncompiled context is allowed"
    prep = json.loads((work / "PREPARATION.json").read_bytes())
    assert prep["graph_sha256"] == sha(work / "DEPENDENCY-GRAPH.json")
    assert sha(work / "scripts/build_connected.py") == CORE_SHA
    assert sha(work / "scripts/AuditTemplate.lean") == AUDIT_SHA
    base_path = work / "scripts/build_with_mathlib_overlay.py"
    auth_path = work / "scripts/build_with_authenticated_overlay.py"
    assert sha(base_path) == prep["namespace_overlay_wrapper_sha256"] == ORIGINAL_OVERLAY
    assert sha(auth_path) == prep["optimized_overlay_sha256"] == ORIGINAL_AUTHENTICATED
    seed_path = work / "CACHE-SEED-RECEIPT.json"
    seed = json.loads(seed_path.read_bytes())
    assert seed["status"] == "PASS_VERIFIED_IMMUTABLE_CACHE_TRANSPORT_ONLY"
    selection = args.selection_manifest.resolve(strict=True)
    assert sha(selection) == seed["selected_manifest_sha256"]
    graph = json.loads((work / "DEPENDENCY-GRAPH.json").read_bytes())
    owned = {m: row for target in graph["targets"].values() for m, row in target["modules"].items()}
    selected = json.loads(selection.read_bytes())
    assert len(selected) == len(owned) and {r["module"] for r in selected} == set(owned)
    entries = []
    for row in selected:
        original_receipt = Path(row["cache_entry"]) / "receipt.json"
        staged = work / ".build/cache" / row["cache_key"]
        assert sha(original_receipt) == sha(staged / "receipt.json") == row["receipt_sha256"]
        rec = json.loads(original_receipt.read_bytes())
        assert rec["module"] == row["module"] and rec["source_sha256"] == owned[row["module"]]["sha256"]
        assert rec["cached_object"] == row["cached_object"] and rec["object_artifacts"] == row["object_artifacts"]
        assert bundle(Path(rec["cached_object"])) == bundle(staged / "artifact.olean") == rec["object_artifacts"]
        entries.append({"module": row["module"], "source_sha256": row["source_sha256"],
            "cache_key": row["cache_key"], "receipt_sha256": row["receipt_sha256"],
            "original_receipt": str(original_receipt), "original_cached_object": row["cached_object"],
            "staged_receipt": str(staged / "receipt.json"), "staged_cached_object": str(staged / "artifact.olean"),
            "object_artifacts": row["object_artifacts"]})
    assert len({entry["original_cached_object"] for entry in entries}) == len(entries)
    manifest = {"status": "PRE_USE_EXACT_SAME_BYTE_CACHE_INSTALL_ALIAS_MANIFEST", "workspace": str(work),
        "graph_sha256": prep["graph_sha256"], "selected_manifest_sha256": sha(selection),
        "cache_seed_receipt_sha256": sha(seed_path), "entries": entries}
    save(work / "CACHE-INSTALL-ALIASES.json", manifest)
    manifest_sha = sha(work / "CACHE-INSTALL-ALIASES.json")
    old_base, old_auth = base_path.read_text(), auth_path.read_text()
    start = old_base.index("    def install(self, base, out, expected):")
    end = old_base.index("    def dependencies(", start)
    new_base = old_base[:start] + INSTALL_METHOD + old_base[end:]
    marker = "sha = lambda p:"
    assert new_base.count(marker) == 1
    new_base = new_base.replace(marker, "CACHE_INSTALL_MANIFEST_SHA = " + repr(manifest_sha) + "\n" + marker)
    compile(new_base, str(base_path), "exec")
    import hashlib
    new_base_sha = hashlib.sha256(new_base.encode()).hexdigest()
    assert old_auth.count(ORIGINAL_OVERLAY) == 1
    new_auth = old_auth.replace(ORIGINAL_OVERLAY, new_base_sha)
    compile(new_auth, str(auth_path), "exec")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/cache-install-transport" / stamp
    evidence.mkdir(parents=True)
    for name, text in [("ORIGINAL-NAMESPACE-OVERLAY.py", old_base), ("ORIGINAL-AUTHENTICATED-OVERLAY.py", old_auth),
                       ("DERIVED-NAMESPACE-OVERLAY.py", new_base), ("DERIVED-AUTHENTICATED-OVERLAY.py", new_auth)]:
        (evidence / name).write_text(text)
    shutil.copyfile(Path(__file__), evidence / "PREPARER.py")
    shutil.copyfile(work / "CACHE-INSTALL-ALIASES.json", evidence / "CACHE-INSTALL-ALIASES.json")
    derivation = {"status": "PRE_USE_FROZEN_STORAGE_ONLY_VERIFIED_INSTALL_DERIVATIVE",
        "workspace": str(work), "graph_sha256": prep["graph_sha256"], "preparer_sha256": sha(Path(__file__)),
        "prior_preparation_sha256": sha(work / "PREPARATION.json"),
        "original_namespace_wrapper_sha256": ORIGINAL_OVERLAY, "original_authenticated_wrapper_sha256": ORIGINAL_AUTHENTICATED,
        "derived_namespace_wrapper_sha256": new_base_sha,
        "derived_authenticated_wrapper_sha256": hashlib.sha256(new_auth.encode()).hexdigest(),
        "alias_manifest_sha256": manifest_sha, "selected_cache_manifest_sha256": sha(selection),
        "cache_seed_receipt_sha256": sha(seed_path), "entries": len(entries), "core_builder_sha256": CORE_SHA,
        "audit_template_sha256": AUDIT_SHA,
        "source_derivation": "Only replace OverlayBuilder.install with original-plus-staged full-bundle verification and local alias transport; add exact manifest hash. Authenticated wrapper only repins that derived wrapper hash.",
        "core_admission_unchanged": "Core still reads the byte-identical selected completed receipt at the original key, checks its original cached_object and actual direct imported companion bundles, and counts actual reuse only after successful install.",
        "input_write_review": "Install never opens input companions or receipts for write. It creates a new output hard link or EXDEV copy; existing outputs must match. Completed cache_result refuses overwrite; compiler outputs remain new attempt paths. No shared chmod or deletion.",
        "original_paths_keys_receipt_bytes_changed": False, "source_or_namespace_guards_changed": False,
        "kernel_compiler_flags_caps_or_audit_policy_changed": False,
        "native_or_global_mathlib_files_changed": False, "compiler_launched": False,
        "evidence": str(evidence.relative_to(ROOT))}
    save(evidence / "RECEIPT.json", derivation)
    save(work / "CACHE-INSTALL-TRANSPORT-DERIVATION.json", derivation)
    base_path.write_text(new_base)
    auth_path.write_text(new_auth)
    assert sha(base_path) == new_base_sha and sha(auth_path) == derivation["derived_authenticated_wrapper_sha256"]
    prep.update(namespace_overlay_wrapper_sha256=new_base_sha,
                optimized_overlay_sha256=derivation["derived_authenticated_wrapper_sha256"],
                cache_install_transport_derivation=derivation)
    save(work / "PREPARATION.json", prep)
    evidence_prep = Path(prep["evidence"])
    if not evidence_prep.is_absolute():
        evidence_prep = ROOT / evidence_prep
    save(evidence_prep / "PREPARATION.json", prep)
    save(ROOT / "CACHE-INSTALL-TRANSPORT-DERIVATION.json", derivation)
    print(json.dumps({k: derivation[k] for k in ["status", "entries", "alias_manifest_sha256", "derived_namespace_wrapper_sha256", "evidence"]}))


if __name__ == "__main__":
    main()
