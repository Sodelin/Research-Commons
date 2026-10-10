#!/usr/bin/env python3
"""Derive an exact four-module overlay with verified cross-filesystem cache transport.

Contributor: Codex / lean_integration_successor, 2026-10-10. The strict compiler,
kernel flags, resource caps, cache authentication and ownership audit are copied
unchanged. Only the namespace adapter's exact owned-module guard and protected
real ancestors expand to the three missing original Mathlib sources. Storage
transport alone falls back to fully hash-checked copies after EXDEV. Original
cache receipt bytes, keys and paths remain unchanged; the strict core is unchanged.
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
ORIGINAL_OVERLAY = "5d57b2cf24966e5286c43d542eb046714a666c685cbce4938ddd261917bb4246"
ORIGINAL_AUTHENTICATED = "cab739f37ee54d8162c827875aaf1726ad6a2184b9e71a1c530745df9475777e"
EXPECTED = {
    "Mathlib.Data.FinEnum": "381c6f445637fdf6bc04a77f062ed2079d9856eeb260b30b609f3c098a3e430a",
    "Mathlib.Algebra.MvPolynomial.Polynomial": "43330a5e928a56af89b209101f98be347937384d2d435f875e2eaff698ccd650",
    "Mathlib.Algebra.MvPolynomial.Funext": "cb1821884a139917b692103a0b267115179cd4e7084da5487857ec49abb0cc7e",
    "Mathlib.Analysis.Convex.Caratheodory": "8e2ead25535366604c2caab3071e5549586f909fe70b885d1c75784e117720f2",
}

OVERLAY_FUNCTION = '''def overlay_mathlib(source_root, context):
    """Real ancestors for exactly four owned original modules; symlink siblings."""
    source = source_root / 'Mathlib'
    assert source.is_dir()
    protected = tuple(tuple(m.split('.')[1:]) for m in sorted(OWNED_MATHLIB))
    links = []

    def stage(src, dst, parts):
        assert not dst.is_symlink(), ('Owned ancestor must be real', dst)
        dst.mkdir(exist_ok=True, parents=True)
        for child in sorted(src.iterdir()):
            rel = parts + (child.name,)
            out = dst / child.name
            if child.is_dir() and any(rel == p[:len(rel)] for p in protected):
                stage(child, out, rel)
            elif any(parts == p[:-1] and
                     (child.name == p[-1] or child.name.startswith(p[-1] + '.'))
                     for p in protected):
                raise RuntimeError('Unexpected external owned artifact: ' + str(child))
            else:
                target = child.resolve(strict=True)
                if out.is_symlink():
                    assert out.resolve(strict=True) == target, ('Overlay target drift', out)
                elif out.exists():
                    raise RuntimeError('Refusing to replace existing overlay path: ' + str(out))
                else:
                    out.symlink_to(target, target_is_directory=child.is_dir())
                links.append({'relative': str(Path('Mathlib', *rel)),
                              'target': str(target), 'directory': child.is_dir()})

    stage(source, context / 'Mathlib', ())
    for parts in protected:
        ancestor = context / 'Mathlib'
        for name in parts[:-1]:
            ancestor = ancestor / name
            assert not ancestor.is_symlink(), ('Owned ancestor must be real', ancestor)
            ancestor.mkdir(exist_ok=True)
    return links
'''


COPY_INSTALL_METHOD = '    def install(self, base, out, expected):\n        """Keep exact receipt paths; copy verified bundles only across filesystems."""\n        import errno\n        assert core.artifact_bundle(base) == expected, (\'Source companion bundle drift\', base)\n        out.parent.mkdir(parents=True, exist_ok=True)\n        for suffix in core.SUFFIXES:\n            source = base.with_suffix(suffix) if suffix in [\'.olean\', \'.ilean\', \'.ir\'] else Path(str(base) + suffix[len(\'.olean\'):])\n            destination = out.with_suffix(suffix) if suffix in [\'.olean\', \'.ilean\', \'.ir\'] else Path(str(out) + suffix[len(\'.olean\'):])\n            if source.exists():\n                if destination.exists():\n                    assert sha(destination) == sha(source), (\'Existing context artifact differs\', destination)\n                else:\n                    try:\n                        os.link(source, destination)\n                    except OSError as error:\n                        if error.errno != errno.EXDEV:\n                            raise\n                        shutil.copy2(source, destination)\n                    assert sha(destination) == sha(source), (\'Transported context artifact differs\', destination)\n        assert core.artifact_bundle(base) == expected, (\'Source companion bundle changed during transport\', base)\n        assert core.artifact_bundle(out) == expected, (\'Installed companion bundle drift\', out)\n\n'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("--label", required=True)
    args = parser.parse_args()
    assert re.fullmatch(r"[A-Za-z0-9_/-]+", args.label) and not args.label.startswith("/") and ".." not in args.label
    original = args.workspace.resolve()
    preparation = json.loads((original / "PREPARATION.json").read_bytes())
    assert sha(original / "DEPENDENCY-GRAPH.json") == preparation["graph_sha256"]
    assert sha(original / "scripts/build_connected.py") == preparation["builder_sha256"]
    assert sha(original / "scripts/AuditTemplate.lean") == preparation["audit_template_sha256"]
    assert preparation["namespace_overlay_wrapper_sha256"] == ORIGINAL_OVERLAY
    assert preparation["optimized_overlay_sha256"] == ORIGINAL_AUTHENTICATED
    base_path = original / "scripts/build_with_mathlib_overlay.py"
    authenticated_path = original / "scripts/build_with_authenticated_overlay.py"
    assert sha(base_path) == ORIGINAL_OVERLAY and sha(authenticated_path) == ORIGINAL_AUTHENTICATED
    graph = json.loads((original / "DEPENDENCY-GRAPH.json").read_bytes())
    owned = {m: row["sha256"] for target in graph["targets"].values()
             for m, row in target["modules"].items() if m.startswith("Mathlib.")}
    assert owned == EXPECTED
    base = base_path.read_text()
    start, end = base.index("def overlay_mathlib("), base.index("\n\nclass OverlayBuilder")
    base = base[:start] + OVERLAY_FUNCTION + base[end:]
    guard = "assert owned == {'Mathlib.Data.FinEnum': FINENUM_SHA}"
    assert base.count(guard) == 1
    base = base.replace(guard, "assert owned == OWNED_MATHLIB")
    assert base.count("    def dependencies(") == 1
    base = base.replace("    def dependencies(", COPY_INSTALL_METHOD + "    def dependencies(", 1)
    definition = "OWNED_MATHLIB = " + repr(EXPECTED) + "\n"
    marker = "sha = lambda p:"
    assert base.count(marker) == 1
    base = base.replace(marker, definition + marker)
    base = base.replace("#!/usr/bin/env python3\n", "#!/usr/bin/env python3\n# Codex / lean_integration_successor: exact pinned four-module namespace and storage adapter.\n", 1)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    name = args.label.replace("/", "_")
    work = ROOT / ".build/proof-extensions" / name / stamp
    evidence = ROOT / "evidence/proof-extensions" / name / stamp
    (work / "scripts").mkdir(parents=True)
    (work / "source-store").mkdir()
    for module, source_hash in preparation["source_pins"].items():
        source = original / "source-store" / (source_hash + ".lean")
        assert sha(source) == source_hash
        shutil.copyfile(source, work / "source-store" / source.name)
        frozen = evidence / "sources" / (module.replace(".", "/") + ".lean")
        frozen.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, frozen)
    shutil.copytree(original / "third-party", work / "third-party")
    for file in ["build_connected.py", "AuditTemplate.lean"]:
        shutil.copyfile(original / "scripts" / file, work / "scripts" / file)
    (work / "scripts/build_with_mathlib_overlay.py").write_text(base)
    new_overlay_hash = sha(work / "scripts/build_with_mathlib_overlay.py")
    authenticated = authenticated_path.read_text()
    assert authenticated.count(ORIGINAL_OVERLAY) == 1
    authenticated = authenticated.replace(ORIGINAL_OVERLAY, new_overlay_hash)
    (work / "scripts/build_with_authenticated_overlay.py").write_text(authenticated)
    for source, filename in [(base_path, "ORIGINAL-MATHLIB-OVERLAY.py"),
                             (authenticated_path, "ORIGINAL-AUTHENTICATED-OVERLAY.py"),
                             (Path(__file__), "PREPARER.py")]:
        shutil.copyfile(source, evidence / filename)
    for destination in [work, evidence]:
        shutil.copyfile(original / "DEPENDENCY-GRAPH.json", destination / "DEPENDENCY-GRAPH.json")
    derivative = {"contributor": "Codex / lean_integration_successor",
        "original_workspace": str(original), "original_preparation_sha256": sha(original / "PREPARATION.json"),
        "original_namespace_overlay_sha256": ORIGINAL_OVERLAY,
        "original_authenticated_overlay_sha256": ORIGINAL_AUTHENTICATED,
        "exact_owned_mathlib_source_pins": EXPECTED,
        "protected_real_ancestors": ["Mathlib/Data", "Mathlib/Algebra/MvPolynomial", "Mathlib/Analysis/Convex"],
        "strict_builder_audit_and_proof_sources_unchanged": True,
        "artifact_storage_transport": "Same-filesystem hard links; EXDEV fallback copy2 with complete source/destination companion SHA256 verification before and after, no cache receipt mutation.",
        "compiler_kernel_cache_and_resource_policies_changed": False,
        "global_mathlib_and_native_artifacts_modified": False}
    preparation = {**preparation, "workspace": str(work), "evidence": str(evidence),
        "namespace_overlay_wrapper_sha256": new_overlay_hash,
        "optimized_overlay_sha256": sha(work / "scripts/build_with_authenticated_overlay.py"),
        "namespace_adapter_derivation": derivative}
    for destination in [work, evidence]:
        save(destination / "PREPARATION.json", preparation)
        save(destination / "NAMESPACE-ADAPTER-DERIVATION.json", derivative)
    save(ROOT / (name.upper() + "-PREPARATION.json"), preparation)
    print(json.dumps({k: preparation[k] for k in ["status", "workspace", "targets", "namespace_overlay_wrapper_sha256", "optimized_overlay_sha256"]}))


if __name__ == "__main__":
    main()
