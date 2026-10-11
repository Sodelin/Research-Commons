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
OLD = 'a2275917b1a844e7b12c5198419f17f51646ff5ac84fee435e0c90f1b129eca3'
NEW = 'a080722170d367fe9aa7420c5c5488fe4c7df73a6d994aba15346a8d2ee4c917'
FCAD = 'fcadb6c4029b06eed32c8d037f294e373d1f91be692807fa477ccbc8edd75f2c'
V2 = 'e3391d165f5f3253a6de2876544ac6568dca3013cbc5d294a6cd55c9a4f39b41'
V3 = '54f1dc3e7326f13b51ddb7427e8fa97bf9908f3dcc6073e5dc2f7e98ef33a230'


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
    refs += [pin(P/'design/history/g6-natural-prefix-repair-static-qc-20261011T0022Z-solver_design_recovery/CE9-REPAIR-V4-PREPARER-STATIC-QC-ATTEMPT1.json','ef1f13df5f32657c43ff7883f4b16c51f71739a716836a6a67c48c05da2f6eb9'),
             pin(P/'design/history/g6-natural-prefix-ce9-failure-saved-qc-20261011T0029Z-solver_design_recovery/SECOND-LIVE-CE9-FAILURE-SAVED-QC-ATTEMPT1.json','473ba9d0faa7a209bc117eb56c7c31620bf4e00d7495abb6ae4b3aa748389bc1')]
    old_pin = pin(B/f'versions/G6OriginalCommonPrefix/{OLD}.lean', OLD)
    new_pin = pin(B/'G6OriginalCommonPrefix.lean', NEW)
    version = pin(B/f'versions/G6OriginalCommonPrefix/{NEW}.lean', NEW)
    old_text = Path(old_pin['path']).read_text(); new_text = Path(new_pin['path']).read_text()
    demand(new_text == Path(version['path']).read_text(), 'current and immutable ce9 bytes')
    expected = old_text
    substitutions = [
        ('type, without the earlier hypotheses being generalized into its match.\n',
         'type, without the earlier hypotheses being generalized into its match.\n'
         'The a2275917 retry leaves only the final recursor-to-match application;\n'
         'local constructor cases make that conversion explicit.\n'),
        ('  · exact hp op hpMem\n',
         '  · cases pre with\n    | nil => exact hp op hpMem\n    | cons a dates => exact hp op hpMem\n')]
    for before, after in substitutions:
        demand(expected.count(before) == 1, 'one exact proof/comment substitution')
        expected = expected.replace(before, after, 1)
    demand(expected == new_text, 'only attribution and final proof-local constructor cases')
    pins = [old_pin, new_pin, version,
            pin(B/'PROPOSAL-FREEZE-V4.json', V2), pin(B/'PROPOSAL-FREEZE-V5.json', V3)]
    old = json.loads((B/'PROPOSAL-FREEZE-V4.json').read_bytes())
    freeze = json.loads((B/'PROPOSAL-FREEZE-V5.json').read_bytes())
    reconstructed = json.loads(json.dumps(freeze))
    repair = reconstructed.pop('repair')
    demand(reconstructed.pop('previous_repair') == old['repair'], 'exact preceding repair retained')
    reconstructed['repair'] = old['repair']
    demand(reconstructed.pop('repair_history') == [old['previous_repair']], 'exact older repair lineage retained')
    reconstructed['previous_repair'] = old['previous_repair']
    demand(repair['previous_freeze_sha256'] == V2 and repair['failed_source_sha256'] == OLD, 'explicit repair lineage')
    demand(reconstructed['sources'][1] == old['sources'][1], 'fcad and all its headers untouched')
    demand([dict(d, line=0) for d in reconstructed['sources'][0]['declarations']] ==
           [dict(d, line=0) for d in old['sources'][0]['declarations']], 'all five original headers unchanged')
    reconstructed['sources'][0] = old['sources'][0]
    reconstructed['utc_created'] = old['utc_created']; reconstructed['status'] = old['status']
    reconstructed['intended_targets'][0] = old['intended_targets'][0]
    demand(reconstructed == old, 'no other freeze/interface/closure/policy change')
    pins.append(pin(REPO/repair['diagnostic'], repair['diagnostic_sha256']))
    demand(repair['diagnostic_sha256'] == '76f19fa35e16014fcb9b6b891640ae4fd0a352be5289f81b24450e1ad57f8db3', 'exact failed stdout')
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
    refs += [pin(P/'design/history/g6-natural-prefix-second-repair-static-qc-20261011T0031Z-solver_design_recovery/A227-REPAIR-V5-PREPARER-STATIC-QC-ATTEMPT2.json','f9cb832971a6e47c96cb26e6729cb10f65c437373c54d8fb5b86fdca27d75df4'),
             pin(P/'design/history/g6-natural-prefix-a227-failure-saved-qc-20261011T0034Z-solver_design_recovery/THIRD-LIVE-A227-FAILURE-SAVED-QC-ATTEMPT1.json','7638bd9e9e5e80b8c3cfa1dc6a46efc36c8adbc7cf93f126e9bddffbadf8e2b7')]
    return {'status':'PASS_STATIC_PROOF_ONLY_A080_SOURCE_QC; new kernel result still required',
            'prior_independent_qc':refs,'pins':pins,'accepted_bindings':bindings,
            'parent_source_pins':provider_pins,'authored_headers':headers,
            'proof_only_changes':['Attributed two-line correction','Final cases pre before unchanged hp application in nil/cons'],
            'unchanged':['All5 prefix top-level headers and hypotheses','beforeNodeWord definition','literal imports/options','fcad source and24headers','139 accepted providers and exact141 closure','all frozen mathematical contexts, scope and downstream interfaces'],
            'qualification':['The third failed run demonstrates that variable recursor/match conversion did not close automatically. The proposed final constructor cases expose the same nil/cons branches; actual kernel goal closure remains pending.',
                'This source gate authorizes no compiler, context or accepted-audit promotion. Any new preparer/context requires its own source/pin/resource gate.',
                'Original natural seed, arbitrary erased initialized Old and full forest/register readers, local all-live support, future no-read, physical/context/bin and G4 boundaries remain those of the prior source QC.',
                'Accepted1504 and separate168/117, historical failed attempts and application/source-fit contracts remain unchanged.']}



def main():
    report = {'schema':'g6_prefix_final_proof_only_repair_independent_static_qc_v1',
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
