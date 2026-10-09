"""Independent authentication of fresh native receipts and raw projections."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'research/2026-10-08-codex-integration-0825z/practical'
FRESH=Path(__file__).resolve().parent.parent/'coordinator/fresh-native'


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    identities={}
    def raw(path):
        body=path.read_bytes();identities[str(path.relative_to(ROOT))]={'sha256':hashlib.sha256(body).hexdigest(),'bytes':len(body)};return body
    def read(path):return json.loads(raw(path))
    summary=read(FRESH/'REPLAY-RESULT.json');built=read(FRESH/'logs/BUILD-RESULT.json')
    assert summary['status']=='PASS' and summary['fresh_execution']
    assert not summary['producer_replacement_or_acceleration'] and summary['cargo_locked_offline_after_provisioning']
    assert built['status']=='PASS' and built['rust_version']=='1.90.0'
    assert built['provisioning_used_network'] and built['cargo_commands_offline_locked']
    for name,digest in summary['inherited_helpers'].items():assert hashlib.sha256(raw(BASE/name)).hexdigest()==digest
    for execution in (FRESH/'logs').glob('*.execution.json'):
        record=read(execution)
        assert record['exit_code']==0 and not record.get('timeout',False)
        prefix=execution.name.removesuffix('.execution.json')
        for suffix in ('stdout','stderr'):
            assert hashlib.sha256(raw(execution.parent/(prefix+'.'+suffix))).hexdigest()==record[suffix+'_sha256']
    before=read(FRESH/'signed-differential/BEFORE.json');after=read(FRESH/'signed-differential/AFTER.json')
    assert before==after
    for relative,row in before['sources'].items():
        body=raw(BASE/'recovered'/relative)
        assert len(body)==row['bytes'] and hashlib.sha256(body).hexdigest()==row['sha256']
    binary=Path(summary['native_binary']);body=binary.read_bytes();assert hashlib.sha256(body).hexdigest()==built['binary']['sha256']==before['binary_sha256']
    result=read(FRESH/'signed-differential/RESULT.json');archived=read(BASE/'signed-differential/RESULT.json')
    assert summary['differential']==result and result['status']=='PASS'
    assert result['cases']==archived['cases'] and len(result['cases'])==39
    physical=('h','u','v','rA','rB','rC','rAB','rR','g');residuals=('root','root_time','h','g','AB1','AB2','BB1')
    for fixture in ('geometry','protocol','row_limit'):
        receipt=read(FRESH/'signed-differential'/(fixture+'.execution.json'))
        assert receipt['exit_code']==0
        for suffix in ('stdin','stdout','stderr'):
            actual=raw(FRESH/'signed-differential'/(fixture+'.'+suffix))
            assert actual==raw(BASE/'signed-differential'/(fixture+'.'+suffix))
            if suffix!='stdin': assert len(actual)==receipt[suffix+'_bytes']
    lines=(FRESH/'signed-differential/geometry.stdout').read_text().splitlines()
    for line,case in zip(lines,result['cases']):
        f=line.split('\t');assert f[:2]==['result',case['id']] and f[10:16]==['0']*6
        actual=dict(status=f[2],refusal=None if f[3]=='-' else f[3],scalar_exp_calls=int(f[4]),precision_fractional_bits=int(f[5]),arithmetic_max_bits=int(f[6]))
        if len(f)==58:
            actual.update(difference_intervals={k:f[16+2*i:18+2*i] for i,k in enumerate(physical)},normalized_absolute_difference_bounds=dict(zip(physical,f[34:43])),maximum_normalized_difference_bound=f[43],signed_residuals={k:f[44+2*i:46+2*i] for i,k in enumerate(residuals)})
        assert actual==case['native']==case['python_projection']
    result=dict(status='PASS',evidence_tier='independent saved fresh-receipt authentication; separate full CLI native execution in test_application.py',
                cases=39,geometries=13,refusals=26,binary_sha256=built['binary']['sha256'],source_identities=identities,
                coordinator_adapter_sha256=hashlib.sha256(raw(FRESH.parent/'native_replay.py')).hexdigest(),
                network_provisioning=True,cargo_locked_offline=True,producer_acceleration_verified=False)
    with a.output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k!='source_identities'},sort_keys=True))


if __name__=='__main__':main()
