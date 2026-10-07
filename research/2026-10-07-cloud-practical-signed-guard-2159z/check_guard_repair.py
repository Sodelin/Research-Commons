"""Only changed loader/parser guards and the three controlling geometries."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import importlib.util
import json
import marshal
import struct
import sys
import tempfile
import time
import signed_receiver as sr


def main():
    root=Path(sys.argv[1]);destination=Path(sys.argv[2]);started=time.time()
    packet=root/'research/2026-10-07-cloud-practical-signed-receiver-2134z'
    old_result_bytes=(packet/'attempt1/RESULT.json').read_bytes()
    assert hashlib.sha256(old_result_bytes).hexdigest()=='611d63a4bb02b458bbbd227a1a76c7b88e26fdffc288df00ebc1796d66d83298'
    old=json.loads(old_result_bytes)
    manifest_bytes=(packet/'PUBLIC-FILES.json').read_bytes()
    assert hashlib.sha256(manifest_bytes).hexdigest()=='878ab5aaf0f5152e5e033f6d17a08bfe1752db146dabb1c3882809559c5bec36'
    manifest=json.loads(manifest_bytes)
    for name,identity in manifest['files'].items():
        blob=(packet/name).read_bytes()
        assert len(blob)==identity['bytes'] and hashlib.sha256(blob).hexdigest()==identity['sha256']
    saved_path=root/'research/2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json'
    saved_bytes=saved_path.read_bytes()
    assert hashlib.sha256(saved_bytes).hexdigest()=='8acf47eadbb01e220f9ebb87746b64f070a0f527bfc0a230e58b316e9f3c6931'
    means=json.loads(saved_bytes)['source_forward_mean_boxes']
    verified=(root/sr.PROVIDER).read_bytes()
    assert hashlib.sha256(verified).hexdigest()==sr.PROVIDER_SHA
    with tempfile.TemporaryDirectory(prefix='signed-guard-fixture-') as directory:
        temporary=Path(directory);provider=temporary/sr.PROVIDER
        provider.parent.mkdir(parents=True);provider.write_bytes(verified)
        marker=temporary/'CACHE_EXECUTED'
        hostile=('from pathlib import Path\nPath('+repr(str(marker))+').write_text("cached")\n')
        stats=provider.stat()
        code=compile(hostile,str(provider),'exec')
        cached=(importlib.util.MAGIC_NUMBER+struct.pack('<III',0,int(stats.st_mtime),stats.st_size)+marshal.dumps(code))
        cache=Path(importlib.util.cache_from_source(str(provider)))
        cache.parent.mkdir();cache.write_bytes(cached)
        math=sr.Arithmetic(temporary,96,4096,2)
        assert math.scalar_exp(F(0),100).lo==1
        assert math.provider_bytes_sha256==sr.PROVIDER_SHA and not marker.exists()
        reader=Path.read_bytes;reads=[]
        def single_read(path):
            if path==provider:
                reads.append(str(path))
                return verified if len(reads)==1 else hostile.encode()
            return reader(path)
        Path.read_bytes=single_read
        try:
            raced=sr.Arithmetic(temporary,96,4096,2)
            raced.authenticate()
            assert raced.scalar_exp(F(0),100).lo==1
            assert len(reads)==1 and not marker.exists()
        finally:Path.read_bytes=reader
        cache_receipt={'status':'PASS','timestamp_and_size_match_source':True,
                       'cached_fixture_sha256':hashlib.sha256(cached).hexdigest(),
                       'marker_absent':not marker.exists(),'provider_reads_in_race_fixture':len(reads)}
    bad={'huge_negative_exponent':('1e-1000000000','RAW_GRAMMAR'),
         'huge_positive_exponent':('1e1000000000','RAW_GRAMMAR'),
         'raw_text_limit':('9'*1000,'RAW_TEXT_LIMIT'),
         'zero_denominator':('1/0','ZERO_DENOMINATOR'),
         'raw_numerator_bits':(str(1<<256),'INPUT_BITS'),
         'raw_denominator_bits':('1/'+str(1<<256),'INPUT_BITS'),
         'decimal_not_supported':('0.5','RAW_GRAMMAR')}
    previous_F=sr.F;fraction_calls=[]
    def forbidden_fraction(*args,**kwargs):
        fraction_calls.append(True)
        raise AssertionError('Fraction allocation occurred before invalid input refusal')
    sr.F=forbidden_fraction
    try:
        for label,(payload,expected) in bad.items():
            try:sr.rational(payload)
            except sr.Refusal as error:assert str(error)==expected,(label,str(error))
            else:raise AssertionError(label)
    finally:sr.F=previous_F
    assert not fraction_calls
    assert sr.rational('-1/20')==F(-1,20) and sr.rational('1/4')==F(1,4)
    exponent_band=dict(means[0]);exponent_band['AC1']=['1e-1000000000','1']
    refusal=sr.receive(root,exponent_band,means[0])
    assert refusal['status']=='UNKNOWN' and refusal['refusal']=='RAW_GRAMMAR'
    common=sr.receive(root,means[0],means[0])
    pair=sr.receive(root,means[0],means[1])
    hull={k:[str(min(F(means[0][k][0]),F(means[1][k][0]))),
             str(max(F(means[0][k][1]),F(means[1][k][1])))] for k in sr.FEATURES}
    combined=sr.receive(root,hull,hull)
    geometries={'common_genuine_forward_band':common,'two_distinct_forward_bands':pair,
                'combined_genuine_forward_band':combined}
    fields=('status','difference_intervals','normalized_absolute_difference_bounds',
            'maximum_normalized_difference_bound','signed_residuals','scalar_exp_calls')
    for key,new in geometries.items():
        for field in fields:assert new[field]==old[key][field],(key,field)
        assert new['verified_provider_bytes_sha256']==sr.PROVIDER_SHA
        assert not new['data_confidence_certificate_issued'] and not new['outer_cover_validated']
    result={'schema':'signed-receiver-guard-repair-controls-v1','status':'PASS',
            'started_unix':started,'ended_unix':time.time(),'loader_controls':cache_receipt,
            'parser_refusal_controls':{key:expected for key,(_,expected) in bad.items()},
            'Fraction_allocations_on_rejected_inputs':len(fraction_calls),
            'receive_exponent_refusal':refusal,'geometry_exactly_matches_original_receipt':True,
            **geometries,'original_ten_packet_files_unchanged':True,
            'original_result_sha256':hashlib.sha256(old_result_bytes).hexdigest(),
            'original_static_source_receipt_sha256':hashlib.sha256(saved_bytes).hexdigest(),
            'new_source_forward_evaluations':0,'observation_rows_replayed':0,
            'data_confidence_certificate_issued':False,'outer_cover_validated':False,
            'source_sha256':{n:hashlib.sha256((Path(__file__).parent/n).read_bytes()).hexdigest()
                             for n in ('signed_receiver.py','check_guard_repair.py','CONTRACT-REPAIR.md')}}
    destination.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','cache_ignored':True,'verified_provider_reads':len(reads),
                      'rejected_input_Fraction_allocations':len(fraction_calls),
                      'geometry_exactly_matches_original_receipt':True,
                      'common_status':common['status'],'other_statuses':[pair['status'],combined['status']],
                      'source_forward_evaluations':0,'observation_rows_replayed':0},sort_keys=True))


if __name__=='__main__':main()
