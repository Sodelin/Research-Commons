"""Integration controls using the statistical peer's unchanged confidence code.

Synthetic count tables test component compatibility, not biological calibration.
A byte-pinned provider is required; a changed peer version needs a fresh review.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json, sys
from sparse_quartet import shapes, graph_from_shape, selected_tree_split_union, split_support_oracle
from abstaining_recovery import recover_with_abstention

HERE = Path(__file__).resolve().parent
EXPECTED_PROVIDER_BLOB = '828b17c948f562560722508940761e54ae1400ed'


def main():
    if not __debug__: raise RuntimeError('Run without -O')
    parser = argparse.ArgumentParser()
    parser.add_argument('--provider', type=Path)
    args = parser.parse_args()
    options = [HERE/'inputs'/'peer_confidence_support.py',
               HERE.parent/'2026-09-30-astra-statistical-bridge'/'confidence_support.py']
    provider = args.provider or next((p for p in options if p.exists()), None)
    if provider is None: raise FileNotFoundError('Provide the pinned peer confidence_support.py with --provider')
    data = provider.read_bytes()
    blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    if blob != EXPECTED_PROVIDER_BLOB: raise ValueError('Peer file differs from the reviewed snapshot')
    spec = importlib.util.spec_from_file_location('peer_confidence_snapshot', provider)
    if spec is None or spec.loader is None: raise ImportError(str(provider))
    peer = importlib.util.module_from_spec(spec); spec.loader.exec_module(peer)
    counts_by_mask = {1:(40000,20000,20000), 4:(20000,20000,40000), 5:(32000,16000,32000)}
    gap, risk = F(1,8), F(1,100)
    n4 = 0
    for counts,mask in [(counts_by_mask[1],1),(counts_by_mask[4],4),
                         (counts_by_mask[5],5),((20000,30000,30000),1)]:
        result = recover_with_abstention(4, lambda q: peer.cf_confidence_masks(counts,gap,risk))
        expected = frozenset(([ (1,3) ] if mask&1 else [])+([ (0,2) ] if mask&4 else []))
        assert result.status == 'complete' and result.recovery.splits == expected
        assert result.oracle_calls == 1
        n4 += 1
    trees = [selected_tree_split_union(graph_from_shape(s,5), [[i] for i in range(5)])
             for s in shapes(1,5)]
    families = {frozenset().union(*(trees[i] for i in range(len(trees)) if mask>>i&1))
                for mask in range(1,1<<len(trees))}
    complete = stopped = 0
    for support in sorted(families,key=lambda x: sorted(x)):
        oracle = split_support_oracle(5,support)
        table = {q:counts_by_mask[oracle(q)] for q in combinations(range(5),4)}
        transcript = []
        def confidence(q):
            transcript.append(q)
            return peer.cf_confidence_masks(table[q],gap,risk)
        result = recover_with_abstention(5, confidence)
        assert result.status == 'complete' and result.recovery.splits == support
        complete += 1
        for unresolved in transcript:
            for replacement in [(1,1,1),(30000,30000,30000)]:
                def with_uncertainty(q):
                    return peer.cf_confidence_masks(replacement if q==unresolved else table[q],gap,risk)
                r = recover_with_abstention(5, with_uncertainty)
                assert r.status == 'inconclusive' and r.recovery is None
                assert r.unresolved_quartet == unresolved
                stopped += 1
    report = {'status':'PASS','created_utc':datetime.now(timezone.utc).isoformat(),
              'consumer_session':'ASTRA-SPARSE-20260930-0938Z',
              'provider_session':'ASTRA-STAT-20260930-0942Z',
              'provider_git_blob':blob,'provider_sha256':hashlib.sha256(data).hexdigest(),
              'four_taxon_complete_cases':n4,'five_taxon_complete_families':complete,
              'ambiguous_or_empty_stopping_controls':stopped,
              'scope':'Actual unchanged peer-provider to sparse-adapter integration on synthetic count tables. Not statistical calibration, jointly realizable locus simulation, or all-level inference.',
              'sha256':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                        for name in ['sparse_quartet.py','abstaining_recovery.py','verify_peer_adapter.py']}}
    (HERE/'verification-peer-integration.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__': main()
