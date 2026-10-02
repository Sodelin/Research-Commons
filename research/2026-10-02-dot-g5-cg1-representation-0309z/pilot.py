"""G5/CG1 representation pilot on the accepted original-source pair.

Public research only. No private workbench imports. Exact support coordinates,
not a measured lineage time series. SHA digests below are integrity/index keys,
never biological or equality certificates. Fraction arithmetic throughout.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from time import perf_counter
import hashlib
import json
import platform
import statistics
import sys
import accepted_binary_source as baseline

ROOT = Path(__file__).resolve().parent
ROSTER = baseline.X
INDEX = {x: i for i, x in enumerate(ROSTER)}


def encode_partition(partition):
    """Joint event: keep which hyperedges occur together, with original IDs."""
    return tuple(sorted(sum(1 << INDEX[x] for x in block) for block in partition))


def decode_partition(masks):
    assert all(0 < m < 1 << len(ROSTER) for m in masks)
    blocks = tuple(frozenset(x for x in ROSTER if m & (1 << INDEX[x])) for m in masks)
    assert sum(len(b) for b in blocks) == len(set().union(*blocks))
    return frozenset(blocks)


def observed_support(G, ages, panel, t):
    """Source truth for H_U(t); input to encoder is the erased joint partition.

    H is identified from exact calendar laws by the accepted germ/chronology
    theorem. This finite pilot does not implement that analytic law parser.
    Positive finite no-merger probability ensures every source assignment has
    the claimed feasible support; posterior weights are NOT assumed uniform.
    """
    support = set()
    for T, _ in baseline.switchings(G):
        group = defaultdict(set)
        for x in panel:
            edge = baseline.active(baseline.ancestral_path(T, x), t, ages)
            group[edge].add(x)
        support.add(frozenset(frozenset(b) for b in group.values()))
    return frozenset(support)


def canonical_support(support):
    return tuple(sorted(encode_partition(partition) for partition in support))


def decode_support(code):
    return frozenset(decode_partition(partition) for partition in code)


def all_partitions(panel):
    if not panel:
        yield frozenset()
        return
    x, rest = panel[0], panel[1:]
    for p in all_partitions(rest):
        yield p | {frozenset((x,))}
        for b in p:
            yield (p - {b}) | {b | {x}}


def haar(values):
    """Rational unnormalized Haar average/detail; all coefficients retained."""
    values = tuple(map(Fraction, values))
    n = len(values)
    assert n > 0 and n & (n - 1) == 0
    if n == 1:
        return values
    avg = tuple((values[i] + values[i+1])/2 for i in range(0, n, 2))
    detail = tuple((values[i] - values[i+1])/2 for i in range(0, n, 2))
    return haar(avg) + detail


def unhaar(coefficients):
    c = tuple(map(Fraction, coefficients))
    if len(c) == 1:
        return c
    m = len(c)//2
    avg = unhaar(c[:m])
    detail = c[m:]
    return tuple(v for a, d in zip(avg, detail) for v in (a+d, a-d))


def support_vector(panel, support):
    coordinates = tuple(sorted(set(encode_partition(p) for p in all_partitions(panel))))
    n = 1
    while n < len(coordinates):
        n *= 2
    code = canonical_support(support)
    return coordinates, tuple(Fraction(int(p in code)) for p in coordinates) + (Fraction(0),)*(n-len(coordinates))


def pair_table(measures):
    """Exactly represented finite shifted-exponential mixture coefficients."""
    return tuple((p, tuple(sorted(m.items()))) for p, m in sorted(measures.items()))


def support_bitmap(coordinates, code):
    lookup = {p:i for i,p in enumerate(coordinates)}
    return sum(1 << lookup[p] for p in code)


def bitmap_decode(coordinates, bitmap):
    assert 0 <= bitmap < 1 << len(coordinates)
    return tuple(p for i,p in enumerate(coordinates) if bitmap & (1 << i))


def merge_groups(code, a, b):
    """Update current lineage membership; original labels are never destroyed."""
    assert a != b and a in code and b in code and not a & b
    return tuple(sorted((set(code)-{a,b}) | {a|b}))


def fingerprint(value):
    # It is deliberately used only AFTER exact encoding, never to accept equality.
    return hashlib.sha256(repr(value).encode()).hexdigest()


def timings(fn, repeats=7, number=1000):
    samples = []
    for _ in range(repeats):
        t = perf_counter()
        for _ in range(number):
            fn()
        samples.append((perf_counter()-t)/number)
    return {"median_seconds": statistics.median(samples), "minimum_seconds": min(samples),
            "repeats": repeats, "operations_per_repeat": number}


def batch_benchmarks(rows):
    """All checked source supports, measured with each backend's full setup.

    The same fixed source-support input is used. Catalogue construction, lookup,
    query masks and every row conversion are charged afresh for each trial.
    Repeated rounds amortize that trial's preparation, not omitted costs.
    """
    panels = tuple(sorted(set(panel for panel,_ in rows)))
    def block_queries(panel):
        return tuple(frozenset(p) for r in range(1,len(panel)+1) for p in combinations(panel,r))
    def raw_run(rounds):
        query_table = {p:block_queries(p) for p in panels}
        for _ in range(rounds):
            answer = tuple(tuple((any(b in event for event in support),all(b in event for event in support))
                           for b in query_table[p]) for p,support in rows)
        return answer
    def bitmap_run(rounds):
        catalogue = {}
        for p in panels:
            coordinates = tuple(sorted(set(encode_partition(event) for event in all_partitions(p))))
            lookup = {event:i for i,event in enumerate(coordinates)}
            masks = tuple(sum(1 << INDEX[x] for x in b) for b in block_queries(p))
            eventbits = tuple(sum(1 << i for i,event in enumerate(coordinates) if b in event) for b in masks)
            catalogue[p] = lookup,eventbits
        converted = tuple((sum(1 << catalogue[p][0][event] for event in canonical_support(support)),catalogue[p][1])
                          for p,support in rows)
        for _ in range(rounds):
            answer = tuple(tuple((bool(bits&b),not bool(bits&~b)) for b in events) for bits,events in converted)
        return answer
    assert raw_run(1) == bitmap_run(1)
    cases = [(rounds,name,fn) for rounds in (1,5,20) for name,fn in (('raw',raw_run),('bitmap',bitmap_run))]
    samples = {(r,n):[] for r,n,_ in cases}
    for repeat in range(7):
        # Alternate backend order, rather than timing every raw run first.
        order = cases if repeat%2 == 0 else list(reversed(cases))
        for rounds,name,fn in order:
            start = perf_counter(); fn(rounds)
            samples[rounds,name].append(perf_counter()-start)
    return {'source_support_rows':len(rows), 'distinct_panel_catalogues':len(panels),
            'block_queries_per_round':sum(2**len(p)-1 for p,_ in rows),
            'full_setup_and_conversion_in_every_trial':True,
            'rounds': {str(r): {name:{'median_seconds':statistics.median(samples[r,name]),
                                    'minimum_seconds':min(samples[r,name]),'repeats':7}
                               for name in ('raw','bitmap')} for r in (1,5,20)},
            'scope':'750 fixture supports, 3150 possible/sure query pairs per round. Inputs are already extracted supports; source construction and law parsing are not measured.'}


def main():
    begin = perf_counter()
    sources = {k: baseline.make_source(k) for k in ("triangle", "star")}
    audits = {k: baseline.audit(*s) for k, s in sources.items()}
    measures = {k: baseline.pair_measures(*s)[0] for k, s in sources.items()}
    assert measures['triangle'] == measures['star']
    pair_codes = {k: pair_table(m) for k, m in measures.items()}
    assert pair_codes['triangle'] == pair_codes['star']
    assert fingerprint(pair_codes['triangle']) == fingerprint(pair_codes['star'])
    # At integer ages 0..31, the observation-identical pair-law mixture
    # coefficients give the same meeting-CDF coordinate vector. This is a
    # deterministic transform of the specified law representation, not direct
    # observation of hidden routes or a sampled biological waveform.
    law_vectors = {k: tuple(sum(w for m,w in measures[k][p].items() if m <= t)
                   for p in sorted(measures[k]) for t in range(32)) for k in sources}
    # Ten pairs, each with exactly 32 evaluation times, all retained.
    wave_codes = {k: tuple(haar(law_vectors[k][i:i+32]) for i in range(0,320,32)) for k in sources}
    assert wave_codes['triangle'] == wave_codes['star']
    assert all(unhaar(c) == law_vectors[k][i*32:(i+1)*32]
               for k in sources for i,c in enumerate(wave_codes[k]))

    checks = 0
    bitmap_checks = 0
    support_rows = []
    for k,(G,ages) in sources.items():
        times = sorted(set(ages.values()))
        times = sorted(set(times + [Fraction(a+b,2) for a,b in zip(times,times[1:])]))
        for r in (1,2,3):
            for panel in combinations(ROSTER,r):
                for t in times:
                    support = observed_support(G, ages, panel, t)
                    support_rows.append((panel,support))
                    code = canonical_support(support)
                    assert decode_support(code) == support
                    coordinates, vec = support_vector(panel, support)
                    bitmap = support_bitmap(coordinates, code)
                    assert bitmap_decode(coordinates, bitmap) == code
                    bitmap_checks += 1
                    assert unhaar(haar(vec)) == vec
                    # All possible/sure exact-block queries are unchanged.
                    for q in range(1,len(panel)+1):
                        for block in map(frozenset, combinations(panel,q)):
                            before = (any(block in p for p in support), all(block in p for p in support))
                            after = (any(block in p for p in decode_support(code)),
                                     all(block in p for p in decode_support(code)))
                            assert before == after
                            checks += 1

    panel = tuple('abc'); t = Fraction(7)
    support = {k: observed_support(*sources[k], panel, t) for k in sources}
    code = {k: canonical_support(s) for k,s in support.items()}
    abc = frozenset('abc')
    assert not any(abc in p for p in support['triangle'])
    assert any(abc in p for p in support['star'])
    assert code['triangle'] != code['star']
    vecs = {k: support_vector(panel,s)[1] for k,s in support.items()}
    haar_triple = {k: haar(v) for k,v in vecs.items()}
    assert haar_triple['triangle'] != haar_triple['star']
    # Pair erasure loses exactly the joint source witness on these admitted sources.
    erased_pairs = {k: {''.join(p): canonical_support(observed_support(*sources[k], p, t))
                    for p in combinations(panel,2)} for k in sources}
    assert erased_pairs['triangle'] == erased_pairs['star']

    # Dropping detail can change support answers. Exact counterexample, no
    # claim that these two synthetic vectors are actual biological source laws.
    loss_a, loss_b = (Fraction(1),Fraction(0)), (Fraction(0),Fraction(1))
    assert haar(loss_a)[0] == haar(loss_b)[0] and loss_a != loss_b
    assert loss_a[0] != loss_b[0]
    merge_checks = 0
    for p in set(all_partitions(ROSTER)):
        codep = encode_partition(p)
        for a,b in combinations(codep,2):
            merged = merge_groups(codep,a,b)
            pa = frozenset(x for x in ROSTER if a & (1 << INDEX[x]))
            pb = frozenset(x for x in ROSTER if b & (1 << INDEX[x]))
            expected = (p-{pa,pb}) | {pa|pb}
            assert decode_partition(merged) == expected
            assert set().union(*decode_partition(merged)) == set(ROSTER)
            merge_checks += 1
    # Current membership alone is a quotient of the full rooted history.
    history_a,history_b = (('a','b'),'c'), ('a',('b','c'))
    assert history_a != history_b
    cs = {k: baseline.clusters(sources[k][0])[0] for k in sources}
    ss = {k: baseline.splits(c) for k,c in cs.items()}
    assert cs['triangle'] != cs['star'] and ss['triangle'] != ss['star']

    raw = support['star']; packed = code['star']; queries = tuple(
        frozenset(p) for r in (1,2,3) for p in combinations(panel,r))
    def raw_queries():
        return tuple((any(b in p for p in raw),all(b in p for p in raw)) for b in queries)
    masks = tuple(sum(1 << INDEX[x] for x in b) for b in queries)
    def packed_queries():
        return tuple((any(b in p for p in packed),all(b in p for p in packed)) for b in masks)
    def packed_with_conversion():
        fresh = canonical_support(raw)
        fresh_masks = tuple(sum(1 << INDEX[x] for x in b) for b in queries)
        return tuple((any(b in p for p in fresh),all(b in p for p in fresh)) for b in fresh_masks)
    def packed_conversion_cached_queries():
        fresh = canonical_support(raw)
        return tuple((any(b in p for p in fresh),all(b in p for p in fresh)) for b in masks)
    coordinate_catalogue,_ = support_vector(panel,raw)
    lookup = {p:i for i,p in enumerate(coordinate_catalogue)}
    supportbits = support_bitmap(coordinate_catalogue,packed)
    blockbits = tuple(sum(1 << i for i,p in enumerate(coordinate_catalogue) if b in p) for b in masks)
    all_bitmap_queries = 0
    for testbits in range(1,1 << len(coordinate_catalogue)):
        testcode = bitmap_decode(coordinate_catalogue,testbits)
        for b,eventbits in zip(masks,blockbits):
            expected = (any(b in p for p in testcode),all(b in p for p in testcode))
            actual = (bool(testbits & eventbits),not bool(testbits & ~eventbits))
            assert actual == expected
            all_bitmap_queries += 1
    def bitmap_queries():
        return tuple((bool(supportbits & b),not bool(supportbits & ~b)) for b in blockbits)
    def bitmap_with_conversion():
        fresh = canonical_support(raw)
        bits = sum(1 << lookup[p] for p in fresh)
        return tuple((bool(bits & b),not bool(bits & ~b)) for b in blockbits)
    def full_bitmap_setup():
        coords = tuple(sorted(set(encode_partition(p) for p in all_partitions(panel))))
        table = {p:i for i,p in enumerate(coords)}
        query_masks = tuple(sum(1 << INDEX[x] for x in b) for b in queries)
        events = tuple(sum(1 << i for i,p in enumerate(coords) if b in p) for b in query_masks)
        return coords,table,events
    def bitmap_one_shot():
        _,table,events = full_bitmap_setup()
        bits = sum(1 << table[p] for p in canonical_support(raw))
        return tuple((bool(bits & b),not bool(bits & ~b)) for b in events)
    assert raw_queries() == packed_queries() == packed_with_conversion() == bitmap_queries() == bitmap_with_conversion()
    assert raw_queries() == packed_conversion_cached_queries() == bitmap_one_shot()
    report = {
        'status': 'PASS_SCOPED_REPRESENTATION_PILOT',
        'attribution': 'dot, representation integration lane, 2026-10-02',
        'baseline': {'accepted_pair_collision_replayed': True, 'sources': audits,
                     'pair_panels': 10,'source_switchings': 16,'pair_cases': 320},
        'new_tested_delta': {'exact_support_query_roundtrips': checks,
            'support_bitmap_roundtrips':bitmap_checks,
            'exhaustive_nonempty_triple_bitmap_block_queries':all_bitmap_queries,
            'original_ID_group_merges_preserved':merge_checks,
            'joint_original_ID_bitmask_encoding_preserves_support': True,
            'rational_full_Haar_roundtrips': True,
            'pair_law_symbolic_identity_fingerprint_and_Haar_still_collide': True,
            'at_time_7_abc_joint_support_separates': True,
            'pair_erasure_of_abc_support_collides': True,
            'cluster_difference': sorted(baseline.fmt_cluster(c) for c in cs['star']-cs['triangle']),
            'split_difference': sorted(baseline.fmt_split(s) for s in ss['star']-ss['triangle'])},
        'triple_support': {k: [list(p) for p in c] for k,c in code.items()},
        'triple_partition_catalogue':[list(p) for p in coordinate_catalogue],
        'triple_support_bitmaps':{k:support_bitmap(coordinate_catalogue,c) for k,c in code.items()},
        'original_ID_roster': list(ROSTER),
        'triple_support_vectors': {k: list(map(str,v)) for k,v in vecs.items()},
        'triple_Haar_coefficients': {k: list(map(str,v)) for k,v in haar_triple.items()},
        'lossy_detail_counterexample': {'inputs': [['1','0'],['0','1']],
                                       'retained_average': '1/2', 'different_first_support_coordinate': True},
        'bytes': {'raw_explicit_label_support_JSON': len(json.dumps([[sorted(b) for b in p] for p in raw])),
                  'bitmask_joint_support_JSON': len(json.dumps(packed)),
                  'support_bitmap_JSON':len(json.dumps(supportbits)),
                  'shared_partition_catalogue_JSON':len(json.dumps(coordinate_catalogue)),
                  'panel_ID_roster_JSON':len(json.dumps(panel)),
                  'time_JSON':len(json.dumps(str(t))),
                  'schema_metadata_required': 'Finite-roster/order, panel, time/change-point, partition enumeration and support-only schema are required; payload lengths are not standalone files',
                  'roster_JSON': len(json.dumps(ROSTER)),
                  'full_8_rational_Haar_JSON': len(json.dumps(list(map(str,haar_triple['star'])))),
                  'full_8_support_indicator_JSON': len(json.dumps(list(map(str,vecs['star']))))},
        'benchmark': {'seven_possible_and_sure_block_queries': {
            'raw':timings(raw_queries),'bitmask_preconverted':timings(packed_queries),
            'bitmask_including_conversion':timings(packed_with_conversion),
            'bitmask_support_conversion_cached_queries':timings(packed_conversion_cached_queries),
            'support_bitmap_preconverted':timings(bitmap_queries),
            'support_bitmap_support_conversion_cached_queries':timings(bitmap_with_conversion),
            'support_bitmap_one_shot_all_setup_and_conversion':timings(bitmap_one_shot)},
            'full_bitmap_catalogue_lookup_querymask_eventmask_setup':timings(full_bitmap_setup),
            'Haar_encoding_8_coordinates':timings(lambda: haar(vecs['star'])),
            'Haar_decoding_8_coordinates':timings(lambda: unhaar(haar_triple['star'])),
            'all_source_support_batch':batch_benchmarks(support_rows),
            'scientific_scope':'Microbenchmark on one 3-label support only. Preconverted methods cache queries. Matched support-conversion methods cache both query mask sets. One-shot includes all dictionary/query setup. No end-to-end or asymptotic speed claim'},
        'limits': ['H_U support supplied from exact source fixtures, not arbitrary observed-law analytic parser',
                   'No biological wavelet measurement, mutation calibration, new target or empirical quality metric',
                   'No source-marginal weights replaced by product weights or hidden-source IDs',
                   'Support bitmap preserves H_U partition support, not full probabilities or calendar law',
                   'Current lineage-group bitmap alone loses rooted merger history; keep full tree and time metadata when required',
                   'No improvement to sharp three-panel boundary, G3/G4 recognition, full Lean closure, or finite-DNA estimation'],
        'classical_vs_new': 'Haar, injective recoding and data processing are classical; new project work is source-faithful adapter and these controls',
        'python': platform.python_version(), 'networkx': baseline.nx.__version__,
        'source_sha256': hashlib.sha256((ROOT/'accepted_binary_source.py').read_bytes()).hexdigest(),
        'pilot_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'elapsed_seconds': perf_counter()-begin}
    (ROOT/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
