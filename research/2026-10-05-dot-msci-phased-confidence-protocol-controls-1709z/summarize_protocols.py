"""Read-only full-byte protocol checks, distinct from independent inverse replay."""
import json
from decimal import Decimal
from pathlib import Path
import integration_core as c
BASE=Path(__file__).resolve().parent
CONTROL_MANIFEST_SHA='ae7889a6d86ba598202b0b3882eafef203b8d785cec5534273d80b8161c77e27'
def terminal(path):
    raw=Path(path).read_bytes()
    if len(raw)>c.MAX_BYTES:raise ValueError('terminal cap')
    def reject(_):raise ValueError('nonfinite terminal number')
    return json.loads(raw,object_pairs_hook=c.no_duplicates,parse_float=Decimal,parse_constant=reject)
def summarize():
    declared=BASE/'declared-protocols';manifest=c.read(declared/'CONTROL-MANIFEST.json',CONTROL_MANIFEST_SHA);records=[]
    for entry in manifest['controls']:
        folder=BASE/'controls'/entry['name'];t=terminal(folder/'TERMINAL.json')
        if t['error'] or t['output_failure'] or t['inventory_failure'] or t['data_confidence_certificate_issued']:raise ValueError('terminal not accepted protocol execution')
        for name,item in t['inventory'].items():
            path=folder/name
            if path.is_symlink() or path.stat().st_size!=item['bytes'] or c.sha(path.read_bytes())!=item['sha256']:raise ValueError('inventory mismatch')
        output=c.read(folder/'COMPOSED-RESULT.json',t['composed_output_sha256'])
        if output['status']!=entry['expected_status'] or output['data_confidence_certificate_issued'] or output.get('data_confidence_certificate_eligible',False) or output['ranked_histories'] is not None:raise ValueError('unexpected protocol status/release')
        req,delta=c.request(declared/entry['request'],entry['request_sha256'])
        if t['request_sha256']!=entry['request_sha256'] or t['source_manifest_sha256']!=c.sha((BASE/'SOURCE-PINS.json').read_bytes()):raise ValueError('runtime request/source binding')
        record={'name':entry['name'],'status':output['status'],'terminal_sha256':c.sha((folder/'TERMINAL.json').read_bytes()),'output_sha256':t['composed_output_sha256'],'data_confidence_certificate_issued':False,'fresh_inverse_executed':t['fresh_inverse_executed'],'expected_counts':entry['expected_counts']}
        if entry['expected_counts'] is None:
            if t['fresh_inverse_executed'] or any((folder/'prepared'/name).exists() for name in ('EXTRACTION.json','CONFIDENCE.json','INVERSE-REQUEST.json')):raise ValueError('refused input released partial inference artifacts')
        else:
            data=c.read(declared/entry['dataset'],entry['dataset_sha256']);counts=c.extract(data,req['expected_loci'],req['selection_sha256'])
            if counts['counts']!=entry['expected_counts']:raise ValueError('literal count oracle mismatch')
            if c.canonical(counts)!=(folder/'prepared/EXTRACTION.json').read_bytes():raise ValueError('count receipt replay mismatch')
            confidence=c.confidence(counts,delta,req['radius_steps'])
            if c.canonical(confidence)!=(folder/'prepared/CONFIDENCE.json').read_bytes():raise ValueError('confidence receipt replay mismatch')
            inverse=c.inverse_request(req,confidence,entry['request_sha256'],c.sha(c.canonical(counts)),c.sha(c.canonical(confidence)))
            if c.canonical(inverse)!=(folder/'prepared/INVERSE-REQUEST.json').read_bytes():raise ValueError('inverse transformation mismatch')
            if output['admission_classification']!='protocol_fixture' or output['coverage_conditional_on_success_claimed']:raise ValueError('protocol/statistical scope mismatch')
            record.update(counts=counts['counts'],m=counts['m'],delta=str(delta),confidence_mode=confidence['mode'],radius=confidence['radius'],union_error_upper=confidence['error_upper_bound'],empty_raw_coordinates=[k for k,v in confidence['raw_moment_projection'].items() if v['empty']],numerical_mode=output['numerical_mode'],complete_numeric_replay=output['complete_numeric_replay'],whole_union_width_target_met=output['whole_union_width_target_met'],retained_boxes=len(output['physical_cover']),widths=output['widths'],journal_frames=len(list((folder/'journal').glob('state-*.json'))),independent_count_confidence_transform_replay_equal=True)
        records.append(record)
    byname={r['name']:r for r in records}
    if c.rational(byname['stricter_delta']['radius'])<c.rational(byname['correlated_twelve']['radius']):raise ValueError('stricter declared delta radius decreased')
    if not byname['incompatible_sixtyfour']['empty_raw_coordinates']:raise ValueError('declared genesis incompatibility not tested')
    return {'schema':'seven-protocol-integration-results-v1','controls':records,'scientifically_admitted_datasets':0,'biological_samples_or_simulator_runs':0,'data_confidence_certificates_issued':0,'empirical_coverage_measured':False,'control_manifest_sha256':CONTROL_MANIFEST_SHA,'registry_sha256':c.TRUSTED_REGISTRY_SHA,'source_manifest_sha256':c.sha((BASE/'SOURCE-PINS.json').read_bytes()),'ranked_histories':None,'interpretation':'protocol arithmetic and fail-closed integration only; scientific/design assumptions not asserted for these records'}
if __name__=='__main__':print(json.dumps(summarize(),sort_keys=True,indent=2))
