#!/usr/bin/env python3
"""Independent bytes/AST-only review; never imports target modules."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

REPO = Path('/workspace/Research-Commons')
P = REPO / 'research/2026-10-10-codex-lean-rust-parity'
B = P / 'lean/proposals/reuse-integration-20261010T2138Z/natural-common-factorization'
OLD = '68e0130ba41f55a7d87d0d8847dff504d53e55fe947020214e57ba42702b010b'
NEW = 'ce9ec8df671d52cb45d3855353faa7c46cffb6660a00cdc2e0f61110602507bd'
FCAD = 'fcadb6c4029b06eed32c8d037f294e373d1f91be692807fa477ccbc8edd75f2c'
V2 = '6a9c47ca70e504477ceb15cbbd98f9f819ffeb4f82805122a004f3b1daec5b49'
V3 = '255102fbe0f74fa115765f32fa9c355328521d4aaa0445698cb3ecabe7c1178e'


def demand(condition, reason):
    if not condition:
        raise AssertionError(reason)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path, expected=None):
    path = Path(path)
    raw = path.read_bytes()
    digest = sha(raw)
    demand(expected is None or digest == expected, 'pin ' + str(path))
    return {'path': str(path), 'sha256': digest, 'bytes': len(raw)}


def without_comments(text):
    out = []; depth = 0; i = 0
    while i < len(text):
        pair = text[i:i+2]
        if pair == '/-':
            depth += 1; out.extend('  '); i += 2
        elif depth and pair == '-/':
            depth -= 1; out.extend('  '); i += 2
        elif not depth and pair == '--':
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.extend(' ' * (end-i)); i = end
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' '); i += 1
    demand(depth == 0, 'balanced comments')
    return ''.join(out)


def imports(text):
    return re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)', without_comments(text), re.M)


def check():
    refs = [
        pin(P/'design/history/g6-natural-common-static-qc-20261010T2350Z-solver_design_recovery/G6-NATURAL-COMMON-STATIC-QC-ATTEMPT2.json',
            'aeb75ab184e093d90204dc249ef41cbf4c7f735eb8beccbcf80fe9de0582c053'),
        pin(P/'design/history/compressed-loader-static-qc-20261010T2356Z-solver_design_recovery/NATURAL141-PREPARER-V3-FACADE-STATIC-QC-ATTEMPT1.json',
            'fbc8d2ca0111b2accad87be86b96335e87a36f0f0036dc8782cbb893555c01ee')]
    old_pin = pin(B/f'versions/G6OriginalCommonPrefix/{OLD}.lean', OLD)
    new_pin = pin(B/'G6OriginalCommonPrefix.lean', NEW)
    version = pin(B/f'versions/G6OriginalCommonPrefix/{NEW}.lean', NEW)
    old_text = Path(old_pin['path']).read_text(); new_text = Path(new_pin['path']).read_text()
    demand(new_text == Path(version['path']).read_text(), 'current and immutable ce9 bytes')
    expected = old_text
    substitutions = [
        ('Codex Lean reuse, 10 October 2026. PROPOSAL; no kernel receipt yet.\n',
         'Codex Lean reuse, 10 October 2026. PROPOSAL; no kernel receipt yet.\n\n'
         'Proof-only compatibility derivative, 11 October 2026, of frozen 68e0130b.\n'
         'The first compiler attempt exposed left-associated append membership and\n'
         'singleton/nil normalization; definitions, statements and imports are unchanged.\n'),
        ('      rw [ih d]\n', '      rw [ih d]\n      simp only [List.append_assoc, List.cons_append, List.nil_append]\n'),
        ('        List.map_cons, List.cons_append, List.append_assoc]\n',
         '        List.map_cons, List.cons_append, List.nil_append, List.append_assoc]\n'),
        ('        intro op hop\n        rcases List.mem_append.mp hop with hboundaryMem | htailMem\n',
         '        intro op hop\n        rw [List.append_assoc] at hop\n        rcases List.mem_append.mp hop with hboundaryMem | htailMem\n'),
        ('  unfold beforeNodeWord at hop\n  rcases List.mem_append.mp hop with hpMem | hremaining\n',
         '  unfold beforeNodeWord at hop\n  rw [List.append_assoc] at hop\n  rcases List.mem_append.mp hop with hpMem | hremaining\n')]
    for before, after in substitutions:
        demand(expected.count(before) == 1, 'one exact proof/comment substitution')
        expected = expected.replace(before, after, 1)
    demand(expected == new_text, 'only attribution and four proof normalization changes')
    pins = [old_pin, new_pin, version,
            pin(B/'PROPOSAL-FREEZE-V2.json', V2), pin(B/'PROPOSAL-FREEZE-V3.json', V3)]
    old = json.loads((B/'PROPOSAL-FREEZE-V2.json').read_bytes())
    freeze = json.loads((B/'PROPOSAL-FREEZE-V3.json').read_bytes())
    reconstructed = json.loads(json.dumps(freeze))
    repair = reconstructed.pop('repair')
    demand(repair['previous_freeze_sha256'] == V2 and repair['failed_source_sha256'] == OLD, 'explicit repair lineage')
    demand(reconstructed['sources'][1] == old['sources'][1], 'fcad and all its headers untouched')
    demand([dict(d, line=0) for d in reconstructed['sources'][0]['declarations']] ==
           [dict(d, line=0) for d in old['sources'][0]['declarations']], 'all five original headers unchanged')
    reconstructed['sources'][0] = old['sources'][0]
    reconstructed['utc_created'] = old['utc_created']; reconstructed['status'] = old['status']
    reconstructed['intended_targets'][0] = old['intended_targets'][0]
    demand(reconstructed == old, 'no other freeze/interface/closure/policy change')
    pins.append(pin(REPO/repair['diagnostic'], repair['diagnostic_sha256']))
    demand(repair['diagnostic_sha256'] == 'd7e88708ec6e041d7a556cd5fb55c51902af19e328aec89bdf763650d5851a8a', 'exact failed stdout')
    pins.append(pin(REPO/repair['diff'], repair['diff_sha256']))
    headers = []
    graph = {}
    for row in freeze['sources']:
        path = REPO/row['path']; pins.append(pin(path, row['sha256']))
        pins.append(pin(REPO/row['immutable_version'], row['sha256']))
        text = path.read_text(); code = without_comments(text)
        demand(imports(text) == row['imports'], 'literal fresh imports')
        demand(not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide)\b', code.replace('#print axioms','')), 'no introduced admission')
        matches = list(re.finditer(r'^(?:private )?(?:noncomputable )?(?:def|theorem)\s+(\w+)', code, re.M))
        demand([m.group(1) for m in matches] == [d['name'] for d in row['declarations']], 'actual declaration inventory')
        for i, (m, d) in enumerate(zip(matches,row['declarations'])):
            span = text[m.start():matches[i+1].start() if i+1<len(matches) else len(text)]
            if d['name'] == 'recordEnd': header = span.split('\n  |',1)[0].strip()
            elif 'theorem' in m.group(0): header = span.split(':= by',1)[0].strip()
            else: header = span.split(':=',1)[0].strip()
            demand(header == d['header'] and sha(header.encode()) == d['sha256'], 'actual unchanged header '+d['name'])
            demand(text[:m.start()].count('\n')+1 == d['line'], 'updated exact line '+d['name'])
            headers.append({'module':row['module'], **d})
        graph[row['module']] = imports(text)
    demand(len(headers) == 29 and freeze['sources'][1]['sha256'] == FCAD, '29 authored heads; fcad untouched')
    bindings = [pin(REPO/row['path'],row['sha256']) for row in freeze['acceptance_bindings']]
    parent = json.loads((P/'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json').read_bytes())
    arm = json.loads((P/'lean/G6-ORIGINAL-PARALLEL-ARM-TRANSPORT-117-ACCEPTANCE.json').read_bytes())
    providers = freeze['exact_composition']['accepted_providers']; provider_pins = []
    demand(len(providers) == len({r['module'] for r in providers}) == 139, '139 exact providers')
    for row in providers:
        path = REPO/row['path']; item = pin(path,row['sha256']); item['module'] = row['module']
        actual = imports(path.read_text()); demand(actual == row['imports'], 'literal provider imports')
        if row['module'] == 'G6OriginalParallelArmTransport':
            demand(row['sha256'] == arm['source']['sha256'], 'separate accepted f40')
        else: demand(row['sha256'] == parent['source_pins'][row['module']], 'accepted1504 provider')
        graph[row['module']] = actual; provider_pins.append(item)
    order = freeze['exact_composition']['topological_modules']; pos = {m:i for i,m in enumerate(order)}
    demand(len(order) == len(pos) == len(graph) == 141 and set(order) == set(graph), 'same141 graph')
    demand(all(pos[p]<pos[m] for m,ps in graph.items() for p in ps if p in graph), 'same topological order')
    seen = set()
    def visit(m):
        if m in seen: return
        seen.add(m)
        for p in graph[m]:
            if p in graph: visit(p)
    visit('G6NaturalCommonForestFactorization'); demand(seen == set(graph), 'reachable exact closure')
    a = P/'lean/scripts/prepare_g6_natural_common_factorization_20261011_v3.py'
    b = P/'lean/scripts/prepare_g6_natural_common_factorization_20261011_v4.py'
    pins += [pin(a,'06c551cc1e9fe218eb3a2f0dc9517ae023293bac059fc07d3c92e3ab5c34c4b7'),
             pin(b,'1ba6a93a39c6323ec82c96c89090cdd645edf5e011c190cab6f4aa8c2ee5f16b')]
    old_ast = ast.parse(a.read_text()); new_ast = ast.parse(b.read_text()); literal_counts = [0,0]; lineage = []
    class Normalize(ast.NodeTransformer):
        def visit_Constant(self,node):
            if node.value == 'proposals/reuse-integration-20261010T2138Z/natural-common-factorization/PROPOSAL-FREEZE-V3.json':
                literal_counts[0] += 1
                return ast.copy_location(ast.Constant(value='proposals/reuse-integration-20261010T2138Z/natural-common-factorization/PROPOSAL-FREEZE-V2.json'),node)
            if node.value == V3:
                literal_counts[1] += 1; return ast.copy_location(ast.Constant(value=V2),node)
            return node
        def visit_Dict(self,node):
            node = self.generic_visit(node)
            for i,key in reversed(list(enumerate(node.keys))):
                if isinstance(key,ast.Constant) and key.value == 'source_repair_derivation':
                    lineage.append(ast.literal_eval(node.values[i])); node.keys.pop(i); node.values.pop(i)
            return node
    normalized = Normalize().visit(new_ast)
    demand(literal_counts == [1,1] and len(lineage) == 1, 'exact two literals and one inert lineage dict')
    demand(ast.dump(normalized,include_attributes=False) == ast.dump(old_ast,include_attributes=False), 'no other preparer executable AST change')
    demand(lineage[0]['prior_preparer_sha256'] == pins[-2]['sha256'] and lineage[0]['failed_source_sha256'] == OLD and lineage[0]['proof_only_repair_sha256'] == NEW, 'exact preparer lineage')
    pins.append(pin(P/'lean/scripts/run_proof_extensions_with_storage_20261011.py','1ecc750032bbe5d0c44ae11dd1ca330db7e607a890c56b2a4c4516b202446b6c'))
    pins.append(pin(P/'lean/proposals/compressed-loader-storage-20261010T235105.986329Z/v3-partial-failure/storage_wrapper.py','d774eb292aa0b819791458c51a9353885d3d31b2bde781b85b3c26829e61c810'))
    return {'status':'PASS_STATIC_PROOF_ONLY_CE9_REPAIR_AND_V4_PREPARER_QC; no new kernel result',
            'prior_independent_qc':refs, 'pins':pins, 'accepted_bindings':bindings,
            'parent_source_pins':provider_pins, 'authored_headers':headers,
            'proof_only_changes':['Attribution comment','Post-IH append/cons/nil normalization','nil_append in phase equality','append_assoc before each of two membership splits'],
            'unchanged':['beforeNodeWord definition','all29 authored headers and all5 prefix hypotheses','literal imports/options','fcad source','139 accepted providers/141 actual closure/145 guard staging','canonical core/storage/facade/native/kernel/transport checks','4GiB180s actual narrow caps; connected6GiB300s separate','76MiB reserve, 2GiB scratch and15GiB memory guard'],
            'preparer_ast_difference':{'freeze_path_literals':1,'freeze_sha_literals':1,'metadata_only_lineage_dict':lineage[0],'all_other_AST_identical':True},
            'qualification':['Source-only compatibility review; the dependent match proof remains as frozen and requires actual diagnostics. No claim all goals now close.',
                'Sole scheduler must separately materialize and authenticate the new context/resource gate before any retry; failed68e WORK must remain in allocation roots.',
                'Natural-bank, erased-history Old, local all-live-at-hybrid, future no-read, physical/context/bin/G4 interfaces retain the prior source QC scope.',
                'No accepted1504/separate117 audit/acceptance, runtime/application/source-fit promotion or master closure changes.']}


def main():
    report = {'schema':'g6_prefix_proof_only_repair_preparer_independent_static_qc_v1',
              'contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),
              'reviewer_sha256':sha(Path(__file__).read_bytes()),'target_imports_or_producers_started':0,
              'machine_verified_proof_claim':False,'accepted_union_modified':False}
    try: report.update(check())
    except Exception as e: report.update(status='FAIL_STATIC_QC',error_type=type(e).__name__,error=str(e))
    out = Path(sys.argv[1])
    with out.open('x') as f: json.dump(report,f,indent=2,ensure_ascii=False,sort_keys=True); f.write('\n')
    print(json.dumps({'status':report['status'],'receipt':str(out),'sha256':sha(out.read_bytes())}))
    return 1 if report['status']=='FAIL_STATIC_QC' else 0


if __name__=='__main__': raise SystemExit(main())
