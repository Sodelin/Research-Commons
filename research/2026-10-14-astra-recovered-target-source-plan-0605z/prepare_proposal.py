#!/usr/bin/env python3
"""Source/metadata-only proposal. No compiler, query, Git, or object access."""
import ast
import datetime
import hashlib
import json
from pathlib import Path
import re
import resource

resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2,) * 2)
resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024**2,) * 2)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SUPPORT = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z'
RECOVERY = ROOT / 'research/2026-10-14-astra-exact-0616-provider-recovery-0555z'
CONSUMER = ROOT / 'research/2026-10-13-dot-g3-certified-consumer-0631z'
FULL = ROOT / 'research/2026-10-14-astra-full-accepted-import-query-0100z'


def exact(path):
    b = path.read_bytes()
    return dict(path=str(path.relative_to(ROOT)), bytes=len(b),
                sha256=hashlib.sha256(b).hexdigest(),
                git_blob=hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest())


inputs = []


def pinned(path, expected):
    row = exact(path)
    if row['sha256'] != expected:
        raise ValueError('pinned input differs: ' + str(path))
    inputs.append(row)
    return json.loads(path.read_text())


catalog = pinned(ROOT / 'research/2026-10-13-astra-unified-solver-0645z/intake/SELECTED-LEAN.json',
                 '77e4fb8bc6812eb6a183b33b3911a19bcc3cfc321e9cf5ea1fe9f30566cdfb14')
full_owned = pinned(ROOT / 'research/2026-10-14-astra-full-owned-plan-0145z/FULL-OWNED-SOURCE-PLAN.json',
                    'b4c7448756ac891e83ebd357c24e75e0c0d2d41ac369ce33744dfdf38170a501')
current = pinned(SUPPORT / 'PROVIDER-SELECTION.json',
                 '0be6bc5d9d9e8e329d8b899bb4d158e1e42188510631d115c60d0a89717ea95b')
old_ext = pinned(SUPPORT / 'EXTERNAL-PLAN.json',
                 'ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10')
full_ext = pinned(FULL / 'evidence/import-query-v2-authenticated/captured/EXTERNAL-PLAN.json',
                  '0c64ed24f1b9d237a7ccee440e9b360cce7ba797079c02d1b0154473866b1d0a')
legacy = pinned(CONSUMER / 'PROVIDER-CLOSURE.json',
                '1aef93f24d16b496f4e1ab499b9bb98749709f4b8029f9d278c34c2ee526339a')
consumer_record = pinned(CONSUMER / 'SOURCE-AND-DEPENDENCIES.json',
                         '5054ed5ebf1ac6674da391ab2ecb11a9aa795d097891edd74d2dde9e8a3e006e')
recovery = pinned(RECOVERY / 'PACKET-MANIFEST.json',
                  '4e7818b1726eb2faa53f930d7b255b9815ddb1dd662847778c64b8fdeee11ac9')
header_path = ROOT / 'research/2026-10-13-astra-follow-on-dependency-plan-2305z/generate_plan.py'
header_pin = exact(header_path)
assert header_pin['sha256'] == '89a30e4bc048196b452a0f6be534d26913c66cc998c80ca63490d4426ad97854'
inputs.append(header_pin)
tree = ast.parse(header_path.read_text())
functions = [x for x in tree.body if isinstance(x, ast.FunctionDef)
             and x.name in {'uncomments', 'imports'}]
assert len(functions) == 2
scope = {'re': re}
exec(compile(ast.Module(body=functions, type_ignores=[]), str(header_path), 'exec'), scope)
literal_imports = scope['imports']

assert len(catalog['modules']) == 1613 and len(full_owned['modules']) == 1641
assert len(old_ext['modules']) == 3591 and len(full_ext['modules']) == 3661
assert full_ext['modules'][:3591] == old_ext['modules']
base = {x['module']: x for x in catalog['modules']}
assert len(base) == 1613
full_by_name = {x['module']: x for x in full_owned['modules']}
selected = {name: dict(module=name, source=x['path'], sha256=x['sha256'],
                      imports=x['imports'], origin='selected1613') for name, x in base.items()}
new_sources = [
    ('G4ProtectedCommonRepresentative', RECOVERY / 'source/G4ProtectedCommonRepresentative.lean',
     '0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04'),
    ('G3CertifiedCommonBoundedWitness', CONSUMER / 'G3CertifiedCommonBoundedWitness.lean',
     '400153aac6adeb8905447f38c616a7d4008605668ffb2d2846dc9a9d5673f94c'),
]
for name, path, expected in new_sources:
    row = exact(path)
    assert row['sha256'] == expected and name not in selected
    selected[name] = dict(module=name, source=str(path.relative_to(ROOT)), sha256=expected,
                          imports=literal_imports(path), origin='recovered_provider' if name.startswith('G4') else 'unchanged_consumer')
assert selected['G3CertifiedCommonBoundedWitness']['imports'] == ['G4ProtectedCommonRepresentative']
assert consumer_record['new_source']['sha256'] == selected['G3CertifiedCommonBoundedWitness']['sha256']
seen = set()
active = set()
external_names = set()


def visit(name):
    if name in seen:
        return
    if name in active:
        raise ValueError('source cycle: ' + name)
    active.add(name)
    row = selected[name]
    path = ROOT / row['source']
    identity = exact(path)
    assert identity['sha256'] == row['sha256'], name
    assert literal_imports(path) == row['imports'], name
    row['identity'] = identity
    for dep in row['imports']:
        if dep in selected:
            visit(dep)
        else:
            external_names.add(dep)
    active.remove(name)
    seen.add(name)


visit('G3CertifiedCommonBoundedWitness')
legacy_map = {x['module']: x for x in legacy['modules']}
provider_names = seen - {'G3CertifiedCommonBoundedWitness'}
assert provider_names == set(legacy_map)
for name in provider_names:
    assert selected[name]['sha256'] == legacy_map[name]['sha256']
    assert selected[name]['imports'] == legacy_map[name]['imports']
order = [x['module'] for x in full_owned['modules'] if x['module'] in seen]
order += [name for name, _, _ in new_sources]
assert set(order) == seen and len(order) == len(seen)
prior = set()
for name in order:
    assert all(dep not in seen or dep in prior for dep in selected[name]['imports'])
    prior.add(name)
for name in seen.intersection(full_by_name):
    f = full_by_name[name]
    assert selected[name]['sha256'] == f['source_sha256'] and selected[name]['imports'] == f['imports']
cur = {x['module']: x for x in current['owned']}
assert len(cur) == 319
for name in seen.intersection(cur):
    assert selected[name]['sha256'] == cur[name]['sha256'] and selected[name]['imports'] == cur[name]['imports']
extra_support = ['Astra.CommonCertificateKernel', 'Astra.PositiveSupportAdapter',
                 'Astra.EmittedSupportExamples', 'AstraPositiveSupport']
extra_support += sorted(x.stem for x in (SUPPORT / 'lean').glob('Certificate_*.lean'))
assert len(extra_support) == 7 and not set(extra_support).intersection(cur)
for name in extra_support:
    path = SUPPORT / 'lean' / (name.replace('.', '/') + '.lean')
    assert path.is_file()
    if name in seen:
        assert exact(path)['sha256'] == selected[name]['sha256']

upstream = {x['module']: (i, x) for i, x in enumerate(full_ext['modules'])}
source_to_upstream = {x['source']: (i, x) for i, x in enumerate(full_ext['modules'])}
assert len(upstream) == len(source_to_upstream) == 3661
owned_mathlib = sorted(n for n in seen if n.startswith('Mathlib.'))
for name in owned_mathlib:
    assert selected[name]['sha256'] == upstream[name][1]['source_sha256']
required_roots = sorted(external_names | set(owned_mathlib))
core_names = sorted(n for n in required_roots if n == 'Init' or n.startswith(('Init.', 'Lean.', 'Std.', 'Lake.')) or n in {'Lean', 'Std', 'Lake'})
root_indices = []
required_indices = set()
core_paths = set()


def visit_external(source):
    if source not in source_to_upstream:
        assert source.startswith('/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/src/lean/'), source
        core_paths.add(source)
        return
    index, row = source_to_upstream[source]
    if index in required_indices:
        return
    required_indices.add(index)
    for dep in row['imports']:
        visit_external(dep)


for name in required_roots:
    if name in core_names:
        continue
    assert name in upstream, 'missing exact external source provider: ' + name
    index, row = upstream[name]
    root_indices.append(dict(module=name, index=index, source_sha256=row['source_sha256']))
    visit_external(row['source'])
required = [dict(index=i, module=full_ext['modules'][i]['module'],
                 source_sha256=full_ext['modules'][i]['source_sha256']) for i in sorted(required_indices)]
not_old = [x for x in required if x['index'] >= 3591]
not_closed = [x for x in required if x['index'] >= 3445]
outside_full = sorted(seen - set(full_by_name))
outside_current = sorted(seen - set(cur))
result = dict(schema='astra_recovered_exact_target_source_proposal_v1',
    status='SOURCE_AND_METADATA_AUTHENTICATED_PROPOSAL_NO_SELECTION_OR_EXECUTION',
    observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), inputs=inputs,
    target='G3CertifiedCommonBoundedWitness', provider='G4ProtectedCommonRepresentative',
    own_sources=[selected[n] for n in order], owned_source_count=len(order),
    source_bytes=sum(selected[n]['identity']['bytes'] for n in order),
    legacy_provider_ledger_exact_set_hash_import_match=True,
    historical_provider_count=len(provider_names), owned_mathlib=owned_mathlib,
    current319_overlap=sorted(seen.intersection(cur)), current319_overlap_count=len(seen.intersection(cur)),
    current326_overlap_count=len(seen.intersection(set(cur) | set(extra_support))),
    current326_extra_source_names=extra_support, outside_current319=outside_current,
    full1641_overlap_count=len(seen.intersection(full_by_name)), outside_full1641=outside_full,
    direct_external_roots=root_indices, toolchain_direct_names=core_names,
    external_source_graph_required=required, external_required_count=len(required),
    external_outside3591=not_old, external_not_in_closed3445_prefix=not_closed,
    toolchain_import_paths=sorted(core_paths),
    source_graph_basis='Literal owned headers plus existing authenticated full3661 source-query plan. No official query of the recovered provider or consumer has run.',
    object_authentication=False, compiler_invocations=0, import_queries=0,
    current_plans_changed=False, new_owned_state_created=False,
    next_gate='Review exact target selection and external delta; authenticate actual dependency receipts/logs/objects/routes before any new compile. Fresh aggregate and full printed types/axioms remain separate. No full1614/1615 public-package claim.')
out = HERE / 'TARGET-SOURCE-PROPOSAL.json'
with out.open('x') as f:
    json.dump(result, f, indent=2)
    f.write('\n')
summary = {k: result[k] for k in ['owned_source_count', 'source_bytes', 'historical_provider_count',
           'owned_mathlib', 'current319_overlap_count', 'current326_overlap_count',
           'full1641_overlap_count', 'outside_full1641', 'external_required_count',
           'external_outside3591', 'external_not_in_closed3445_prefix']}
summary['proposal_sha256'] = exact(out)['sha256']
print(json.dumps(summary))
