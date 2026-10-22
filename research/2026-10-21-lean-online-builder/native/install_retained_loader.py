"""Stage authored loader sources only; never import or invoke a native builder."""
import hashlib
import json
from pathlib import Path
from delta_reuse_loader import SCRIPTS, OUTER, profile_for


def install_loader(destination):
    destination = Path(destination).resolve()
    if any((p/'.git').exists() for p in [destination, *destination.parents]):
        raise ValueError('NON_GIT_SOURCE_DESTINATION_REQUIRED')
    if any(p.is_symlink() for p in destination.rglob('*')):
        raise ValueError('SOURCE_SYMLINK_REFUSED')
    graph = (destination/'DEPENDENCY-GRAPH.json').read_bytes()
    selection = (destination/'SOURCE-SELECTION.json').read_bytes()
    template = (destination/'scripts/AuditTemplate.lean').read_bytes()
    profile = profile_for(graph, selection, template)
    outer = destination/'start_new_context.sh'
    if hashlib.sha256(outer.read_bytes()).hexdigest() != OUTER:
        raise ValueError('MANDATORY_REFUSAL_CHANGED')
    here = Path(__file__).resolve().parent
    files = [(here/'retained-loader'/name, destination/'scripts'/name, wanted)
             for name, wanted in SCRIPTS.items()]
    adapter = here/'delta_reuse_loader.py'
    files.append((adapter, destination/'scripts'/adapter.name,
                  hashlib.sha256(adapter.read_bytes()).hexdigest()))
    # Check the entire source inventory before writing any new script.
    for src, dst, wanted in files:
        if src.is_symlink() or hashlib.sha256(src.read_bytes()).hexdigest() != wanted:
            raise ValueError('RETAINED_SOURCE_CHANGED: '+src.name)
        if dst.exists() and (dst.is_symlink() or hashlib.sha256(dst.read_bytes()).hexdigest() != wanted):
            raise ValueError('EXISTING_SOURCE_DIFFERS: '+dst.name)
    for src, dst, wanted in files:
        if not dst.exists():
            with dst.open('xb') as stream:
                stream.write(src.read_bytes())
        if hashlib.sha256(dst.read_bytes()).hexdigest() != wanted:
            raise ValueError('STAGED_SOURCE_READBACK_MISMATCH: '+dst.name)
    manifest = {
        'source_only': True, 'compiler_invoked': False, 'controller': 'UNBOUND',
        'scripts': {dst.name: wanted for _, dst, wanted in files},
        'owned_mathlib': profile['owned_mathlib'],
        'fresh_original_components_allowed': 0, 'delta_source_allowlist': profile['added'],
        'mandatory_outer_sha256': OUTER,
        'original_sources': 'research/2026-10-12-dot-accepted-connected-union1613-1737z/scripts',
        'source_commit': '1138a5b1a281caa00b38e0976db95b586938754b',
        'native_execution_permission': False,
    }
    target = destination/'BUILD-LOADER.json'
    with target.open('x') as stream:
        stream.write(json.dumps(manifest, indent=2)+'\n')
    return manifest
