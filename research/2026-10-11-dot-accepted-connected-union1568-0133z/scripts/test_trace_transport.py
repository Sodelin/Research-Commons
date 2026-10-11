from pathlib import Path
import tempfile,gzip,json,hashlib
from completed_trace_transport import validate,compress_completed,sha
P=Path(__file__).resolve().parents[1]; results=[]
with tempfile.TemporaryDirectory(dir=P,prefix='trace-negative-') as td:
 root=Path(td);raw=b'exact saved loader bytes\n';g=root/'trace.gz';g.write_bytes(gzip.compress(raw,mtime=0));entry={'raw_path':'raw','archive_path':'trace.gz','raw_sha256':hashlib.sha256(raw).hexdigest(),'raw_bytes':len(raw),'archive_sha256':sha(g)}
 a=root/'.build/runs/control/attempts/1';a.mkdir(parents=True);entry['raw_path']=str((a/'NATIVE-LOADER.1').relative_to(root));r0=a/'receipt.json';r0.write_text(json.dumps({'status':'PASS_FRESH_KERNEL_CHECK','exit_code':0,'source_and_imports_stable':True,'native_loader_outputs':[{'path':str(root/entry['raw_path']),'sha256':entry['raw_sha256']}]}));entry.update(receipt_path=str(r0.relative_to(root)),receipt_sha256=sha(r0))
 assert validate(root,entry,True);results.append('valid_roundtrip_pass')
 saved=r0.read_bytes();r0.write_bytes(b'{}')
 try:validate(root,entry,True);raise RuntimeError('changed receipt accepted')
 except AssertionError as e:assert e.args[0][0]=='RECEIPT_BINDING_DRIFT';results.append('changed_receipt_rejected')
 r0.write_bytes(saved)
 detached=dict(entry,raw_path=str((a/'NATIVE-LOADER.2').relative_to(root)))
 try:validate(root,detached,True);raise RuntimeError('detached trace accepted')
 except AssertionError as e:assert e.args[0][0]=='DETACHED_TRACE_MAPPING';results.append('detached_trace_mapping_rejected')
 g.rename(root/'saved.gz')
 try:validate(root,entry,True);raise RuntimeError('missing archive accepted')
 except AssertionError as e:assert e.args[0][0]=='MISSING_ARCHIVE';results.append('missing_archive_rejected')
 g.write_bytes(b'corrupt')
 try:validate(root,entry,True);raise RuntimeError('corrupt archive accepted')
 except AssertionError as e:assert e.args[0][0]=='CORRUPT_ARCHIVE';results.append('corrupt_archive_rejected')
 r0.unlink()
 attempt=root/'.build/runs/test/attempts/00001-test';attempt.mkdir(parents=True);trace=attempt/'NATIVE-LOADER.1';trace.write_bytes(raw);receipt=attempt/'receipt.json';r={'status':'FAILED_OR_RESOURCE','exit_code':1,'source_and_imports_stable':True,'native_loader_outputs':[{'path':str(trace),'sha256':sha(trace)}]};receipt.write_text(json.dumps(r));assert compress_completed(root,True)==0 and trace.read_bytes()==raw;results.append('failed_trace_untouched')
 receipt.unlink();assert compress_completed(root,True)==0 and trace.read_bytes()==raw;results.append('active_or_incomplete_trace_untouched')
 r.update(status='PASS_FRESH_KERNEL_CHECK',exit_code=0);r['native_loader_outputs'][0]['sha256']='0'*64;receipt.write_text(json.dumps(r))
 try:compress_completed(root,True);raise RuntimeError('wrong receipt hash accepted')
 except AssertionError as e:assert e.args[0][0]=='RECEIPT_TRACE_MISMATCH';assert trace.read_bytes()==raw;results.append('wrong_receipt_digest_rejected_raw_preserved')
 r['native_loader_outputs'][0]['sha256']=sha(trace);receipt.write_text(json.dumps(r));assert compress_completed(root,True)==1 and not trace.exists();assert compress_completed(root,True)==1;results.append('completed_pass_roundtrip_and_idempotence_pass')
 report={'status':'PASS_BOUNDED_POSITIVE_AND_NEGATIVE_TRANSPORT_CONTROLS','checks':results,'real_run_traces_mutated_by_test':False,'helper_sha256':sha(Path(__file__).with_name('completed_trace_transport.py'))};(P/'TRACE-TRANSPORT-CONTROLS.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
