"""Independent saved-evidence recount; no scientific provider imported."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'research/2026-10-08-codex-integration-0825z/practical'
PHYSICAL = ('h', 'u', 'v', 'rA', 'rB', 'rC', 'rAB', 'rR', 'g')
RESIDUALS = ('root', 'root_time', 'h', 'g', 'AB1', 'AB2', 'BB1')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    identities = {}
    def read(path):
        raw = path.read_bytes()
        identities[str(path.relative_to(ROOT))] = {'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw)}
        return json.loads(raw)
    signed = read(BASE / 'signed-differential/RESULT.json')
    lines = (BASE / 'signed-differential/geometry.stdout').read_text().splitlines()
    assert len(lines) == len(signed['cases']) == 39
    for line, case in zip(lines, signed['cases']):
        f = line.split('\t')
        assert len(f) in (16, 58) and f[:2] == ['result', case['id']]
        assert f[9] == 'native_exact_interval_core' and f[10:16] == ['0'] * 6
        actual = dict(status=f[2], refusal=None if f[3] == '-' else f[3],
                      scalar_exp_calls=int(f[4]), precision_fractional_bits=int(f[5]), arithmetic_max_bits=int(f[6]))
        if len(f) == 58:
            actual.update(difference_intervals={k: f[16+2*i:18+2*i] for i,k in enumerate(PHYSICAL)},
                          normalized_absolute_difference_bounds=dict(zip(PHYSICAL, f[34:43])),
                          maximum_normalized_difference_bound=f[43],
                          signed_residuals={k: f[44+2*i:46+2*i] for i,k in enumerate(RESIDUALS)})
        assert actual == case['native'] == case['python_projection']
    assert sum(len(line.split('\t')) == 58 for line in lines) == 13
    assert not signed['data_confidence_certificate_issued'] and not signed['compatible_source_existence_verified']

    numerical = {}
    for name in ('original-baseline', 'original-multistage', 'finite-data'):
        record = read(BASE / name / 'RESULT.json')
        request = read(BASE / name / 'REQUEST.json')
        checked = read(BASE / name / 'checker.stdout')
        assert checked == record['checker'] and checked['details']['complete_numeric_replay']
        widths = {}
        for k in PHYSICAL:
            lo = min(Q(c['box'][k][0]) for c in checked['physical_cover'])
            hi = max(Q(c['box'][k][1]) for c in checked['physical_cover'])
            w = (hi-lo)/(Q(request['box'][k][1])-Q(request['box'][k][0]))
            assert w == Q(checked['widths'][k]['normalized_ratio'])
            widths[k] = str(w)
        numerical[name] = dict(status=checked['status'], normalized_widths=widths,
                               maximum=str(max(map(Q,widths.values()))), frames=checked['details']['journal_frames'])
        journal_rows = record.get('journal', [dict(name=p.name, sha256=p.stem.rsplit('-',1)[1], bytes=p.stat().st_size)
                                               for p in sorted((BASE / name / 'journal').glob('state-*.json'))])
        assert len(journal_rows) == checked['details']['journal_frames']
        for row in journal_rows:
            raw = (BASE / name / 'journal' / row['name']).read_bytes()
            assert hashlib.sha256(raw).hexdigest() == row['sha256'] and len(raw) == row['bytes']
    assert all(Q(x) <= Q(1,20) for x in numerical['original-multistage']['normalized_widths'].values())
    assert numerical['original-multistage']['maximum'] == '17394377843899475/4611686018427387904'
    assert all(Q(x) == 1 for x in numerical['finite-data']['normalized_widths'].values())

    dataset = read(ROOT / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration/declared-model/DATASET.json')
    extracted = read(BASE / 'finite-data/EXTRACTION.json')
    assert len(dataset['loci']) == extracted['m'] == 1024
    counts = {k: 0 for k in extracted['feature_order']}
    signs = {'A':1, 'C':1, 'G':-1, 'T':-1}
    for locus in dataset['loci']:
        for k in counts:
            x,y = extracted['pairs'][k[:2]]
            parity = 1
            for site in range(int(k[-1])):
                parity *= signs[locus['calls'][x][site]] * signs[locus['calls'][y][site]]
            counts[k] += (1+parity)//2
    assert counts == extracted['counts']
    confidence = read(BASE / 'finite-data/CONFIDENCE.json')
    request = read(BASE / 'finite-data/REQUEST.json')
    radius = Q(3301,65536)
    assert Q(confidence['radius']) == radius
    expected = {k:[str(max(Q(0),Q(n,1024)-radius)),str(min(Q(1),Q(n,1024)+radius))] for k,n in counts.items()}
    assert expected == request['features'] == confidence['shifted_mean_box']
    conversion = read(BASE / 'finite-data/MEAN-CONVERSION.json')
    raw_means = {k:[str(max(Q(0),2*Q(lo)-1)),str(min(Q(1),2*Q(hi)-1))] for k,(lo,hi) in expected.items()}
    assert conversion['actual'] == raw_means
    pair = read(BASE / 'finite-data/PAIR-WIDTH-OBSTRUCTION.json')
    archive_path = ROOT / 'research/2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json'
    archive = read(archive_path)
    assert identities[str(archive_path.relative_to(ROOT))]['sha256'] == pair['source_mean_archive_sha256']
    assert archive['source_parameter_points'] == pair['source_parameter_points']
    for point in archive['source_parameter_points']:
        for k,v in point.items():
            assert Q(request['box'][k][0]) <= Q(v[0]) == Q(v[1]) <= Q(request['box'][k][1])
    for means in archive['source_forward_mean_boxes']:
        for k,(lo,hi) in means.items():
            assert Q(expected[k][0]) <= Q(lo) <= Q(hi) <= Q(expected[k][1])
    delta = abs(Q(pair['source_parameter_points'][0]['rA'][0])-Q(pair['source_parameter_points'][1]['rA'][0])) / (Q(6)-Q(1,2))
    assert delta == Q(3,55) > Q(1,20)
    result = dict(status='PASS', evidence_tier='independent static recount of archived evidence; no numerical provider execution',
                  signed_cases=39, completed_geometries=13, refusals=26, numerical=numerical,
                  finite_data_counts=counts, normalized_rA_separation=str(delta), source_identities=identities,
                  statistical_sampling_law_verified=False, biological_accuracy_verified=False)
    with a.output.open('x') as f:
        json.dump(result,f,indent=2,sort_keys=True); f.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('source_identities','numerical')},sort_keys=True))


if __name__ == '__main__':
    main()
