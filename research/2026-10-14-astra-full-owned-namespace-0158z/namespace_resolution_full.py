"""Bind the exact full source graph to authenticated external namespaces.

No compiler or subprocess is invoked. Source/object identities must already have
passed the caller's complete external receipt authentication.
"""
import hashlib
import json
import os
from pathlib import Path

ENV_KEYS = ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_NUM_THREADS', 'LEAN_STACK_SIZE_KB',
            'LEAN_IMPORT_WORKERS', 'MIMALLOC_ARENA_RESERVE', 'RAYON_NUM_THREADS')
PATH_SOURCE_SHA = '52cf9aa41a82db18d0d3c93bf6257d064f773af9e62b8b43be89ce1b0e00055f'
LOADED_SHA = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OWNED_PLAN = ROOT / 'research/2026-10-14-astra-full-owned-plan-0145z/FULL-OWNED-SOURCE-PLAN.json'
OWNED_PLAN_SHA = 'b4c7448756ac891e83ebd357c24e75e0c0d2d41ac369ce33744dfdf38170a501'
EXTERNAL_PLAN = ROOT / 'research/2026-10-14-astra-full-accepted-import-query-0100z/evidence/import-query-v2-authenticated/captured/EXTERNAL-PLAN.json'
EXTERNAL_PLAN_SHA = '0c64ed24f1b9d237a7ccee440e9b360cce7ba797079c02d1b0154473866b1d0a'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def binding_digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def selected_environment(env):
    # compile_one sets this final allocator control in its child environment.
    return {**{key: env[key] for key in ENV_KEYS}, 'MALLOC_ARENA_MAX': '1'}


def first_namespace_root(name, roots):
    head = name.split('.')[0]
    for root in roots:
        if (root / head).is_dir() or (root / (head + '.olean')).exists():
            return root
    return None


def bind_routes(modules, source_root, build, repos, env, external_rows,
                external_sources, lean_bin):
    if digest(__file__) != LOADED_SHA:
        raise ValueError('loaded namespace helper differs from current source')
    if digest(OWNED_PLAN) != OWNED_PLAN_SHA or digest(EXTERNAL_PLAN) != EXTERNAL_PLAN_SHA:
        raise ValueError('full selected source plan changed')
    planned = json.loads(OWNED_PLAN.read_text())
    upstream = json.loads(EXTERNAL_PLAN.read_text())['modules']
    if len(modules) != 1641 or len(upstream) != 3661:
        raise ValueError('full namespace graph scope differs')
    if [(r['module'], r['sha256']) for r in modules] != [
            (r['module'], r['source_sha256']) for r in planned['modules']]:
        raise ValueError('full owned source order or selected versions differ')
    if external_sources != {r['module']: r for r in upstream}:
        raise ValueError('full external source selection differs')
    if set(external_rows) != set(external_sources):
        raise ValueError('full external receipt selection differs')
    if (source_root != Path(planned['materialized_source'])
            or build != Path(planned['proposed_fresh_owned_state']) / '.lake/build/lib/lean'):
        raise ValueError('full selected source or isolated owned state differs')
    official = lean_bin.parent / 'src/lean/Lean/Util/Path.lean'
    if digest(official) != PATH_SOURCE_SHA:
        raise ValueError('official namespace resolution source differs')
    roots = [p / '.lake/build/lib/lean' for p in repos]
    if any(not p.is_absolute() or p.resolve() != p for p in roots + [build]):
        raise ValueError('namespace roots must be canonical absolute paths')
    if env['LEAN_PATH'].split(os.pathsep) != [str(p) for p in roots]:
        raise ValueError('external namespace root order differs from pinned setup')
    if len(set(roots + [build])) != len(roots) + 1:
        raise ValueError('owned library overlaps external roots')
    for name, row in external_sources.items():
        root = first_namespace_root(name, roots)
        if root is None or str(root / (name.replace('.', '/') + '.olean')) != row['target']:
            raise ValueError('external namespace route differs from authenticated graph: ' + name)
    non_mathlib = [row['module'] for row in modules if not row['module'].startswith('Mathlib.')]
    for name in non_mathlib:
        if first_namespace_root(name, roots) is not None:
            raise ValueError('external top namespace masks selected owned module: ' + name)
    equivalences = []
    for row in modules:
        name = row['module']
        if not name.startswith('Mathlib.'):
            continue
        upstream = external_sources[name]
        authenticated = external_rows[name]
        selected_source = source_root / (name.replace('.', '/') + '.lean')
        if not (digest(selected_source) == row['sha256'] == upstream['source_sha256']
                == authenticated['source_sha256'] == digest(upstream['source'])):
            raise ValueError('selected/upstream Mathlib source differs: ' + name)
        root = first_namespace_root(name, roots)
        if root is None:
            raise ValueError('selected Mathlib namespace absent: ' + name)
        selected_object = root / (name.replace('.', '/') + '.olean')
        if str(selected_object) != upstream['target'] or str(selected_object) not in authenticated['artifacts']:
            raise ValueError('first external Mathlib route differs from authenticated target: ' + name)
        for path, expected in authenticated['artifacts'].items():
            if digest(path) != expected:
                raise ValueError('selected external Mathlib artifact differs: ' + path)
        equivalences.append(dict(module=name, selected_source=str(selected_source),
            selected_source_sha256=row['sha256'], upstream_source=upstream['source'],
            selected_external_object=str(selected_object),
            selected_external_artifacts=authenticated['artifacts'],
            external_receipt_sha256=authenticated['receipt_sha256'],
            cloned_owned_target=str(build / (name.replace('.', '/') + '.olean')),
            compiler_uses='authenticated_external_object', fresh_compilation=False))
    if len(equivalences) != 11:
        raise ValueError('this exact full successor requires eleven selected Mathlib equivalences')
    resolved_env = dict(env, LEAN_PATH=os.pathsep.join(map(str, roots + [build])))
    binding = dict(schema='astra_full_owned_namespace_resolution_v1',
        full_owned_source_plan_sha256=OWNED_PLAN_SHA,
        full_external_source_plan_sha256=EXTERNAL_PLAN_SHA,
        official_rule_source=str(official), official_rule_sha256=PATH_SOURCE_SHA,
        helper_sha256=LOADED_SHA, external_roots=list(map(str, roots)),
        owned_root=str(build), selected_environment=selected_environment(resolved_env),
        compiler_common_options=['-j', '1', '-s', '8192', '-R', str(source_root)],
        selected_mathlib_equivalences=equivalences,
        owned_namespaces_checked=sorted({name.split('.')[0] for name in non_mathlib}),
        research_namespace_policy='reject every earlier top namespace directory or root .olean',
        full_selected_mathlib_source_equivalence_checked=True,
        historical_object_or_elaborated_type_equivalence_claimed=False)
    return resolved_env, binding
