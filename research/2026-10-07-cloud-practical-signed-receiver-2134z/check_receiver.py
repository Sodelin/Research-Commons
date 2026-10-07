"""New receiver controls on static source-mean receipts; never load data rows."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import sys
import time
import signed_receiver as sr


def contains(result,key,value):
    lo,hi=map(F,result['difference_intervals'][key])
    assert lo<=value<=hi,(key,value,lo,hi)


def main():
    root=Path(sys.argv[1]);destination=Path(sys.argv[2])
    started=time.time()
    source=root/'research/2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json'
    blob=source.read_bytes()
    assert hashlib.sha256(blob).hexdigest()=='8acf47eadbb01e220f9ebb87746b64f070a0f527bfc0a230e58b316e9f3c6931'
    saved=json.loads(blob)
    means=saved['source_forward_mean_boxes'];points=saved['source_parameter_points']
    common=sr.receive(root,means[0],means[0])
    for key in sr.PHYSICAL:contains(common,key,F(0))
    pair=sr.receive(root,means[0],means[1])
    for key in sr.PHYSICAL:
        contains(pair,key,F(points[0][key][0])-F(points[1][key][0]))
    assert pair['status']=='UNKNOWN'
    hull={key:[str(min(F(means[0][key][0]),F(means[1][key][0]))),
               str(max(F(means[0][key][1]),F(means[1][key][1])))] for key in sr.FEATURES}
    combined=sr.receive(root,hull,hull)
    assert combined['status']=='UNKNOWN'
    for key in sr.PHYSICAL:
        contains(combined,key,F(points[0][key][0])-F(points[1][key][0]))
    broad={key:['1/2','1'] for key in sr.FEATURES}
    denominator=sr.receive(root,broad,broad)
    assert denominator['status']=='UNKNOWN' and denominator['refusal']=='ROOT_DENOMINATOR'
    refusal=sr.receive(root,means[0],means[0],max_exp_calls=0)
    assert refusal['status']=='UNKNOWN' and refusal['refusal']=='EXP_CALLS'
    malformed=dict(means[0]);malformed['AC1']=[True,'1']
    invalid=sr.receive(root,malformed,means[0])
    assert invalid['status']=='UNKNOWN' and invalid['refusal']=='RATIONAL_INPUT'
    math=sr.Arithmetic(root,96,4096,0)
    product=math.interval(-2,-1)*math.interval(3,4)
    assert product.lo<=-8 and product.hi>=-3
    quotient=math.interval(1)/math.interval(2,3)
    assert quotient.lo<=F(1,3) and quotient.hi>=F(1,2)
    rounded=math.interval(F(1,10))
    assert rounded.lo<=F(1,10)<=rounded.hi
    result={'schema':'signed-original-source-receiver-controls-v1','status':'PASS',
            'started_unix':started,'ended_unix':time.time(),
            'controls':{'rounding_signed_product_positive_division':'PASS',
                        'two_actual_point_differences_preserved':'PASS',
                        'combined_band_retains_actual_pair':'PASS',
                        'positive_denominator_guard':'PASS','exp_budget_refusal':'PASS',
                        'malformed_boolean_refusal':'PASS'},
            'common_genuine_forward_band':common,'two_distinct_forward_bands':pair,
            'combined_genuine_forward_band':combined,'denominator_guard':denominator,
            'changed_budget_refusal':refusal,'malformed_refusal':invalid,
            'source_receipt_sha256':hashlib.sha256(blob).hexdigest(),
            'new_source_forward_evaluations':0,'observation_rows_replayed':0,
            'data_confidence_certificate_issued':False,'outer_cover_validated':False,
            'common_forward_input_geometry_certified':common['status']=='CONDITIONAL_PAIR_WIDTH_CERTIFIED',
            'actual_observed_confidence_band_admitted':False,
            'source_sha256':{name:hashlib.sha256((Path(__file__).parent/name).read_bytes()).hexdigest()
                             for name in ('signed_receiver.py','check_receiver.py','CONTRACT.md')}}
    destination.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':result['status'],'common_status':common['status'],
                      'common_maximum_normalized_difference_bound':common.get('maximum_normalized_difference_bound'),
                      'two_point_status':pair['status'],'combined_band_status':combined['status'],
                      'new_source_forward_evaluations':0,'observation_rows_replayed':0},sort_keys=True))


if __name__=='__main__':main()
