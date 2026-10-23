"""Exercise the real shared validator; fixtures stay in RAM and writes are spied."""
import base64,copy,importlib.util,json,pathlib,subprocess,unittest
from unittest.mock import patch
P=pathlib.Path(__file__).with_name('refresh.py');spec=importlib.util.spec_from_file_location('refresh',P);refresh=importlib.util.module_from_spec(spec);spec.loader.exec_module(refresh)
class RefreshBoundary(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.raw=(refresh.ROOT/'dist/claims.json').read_bytes();cls.overlay_raw=(refresh.ROOT/'dist/subjective-reuse-ranking.json').read_bytes()
  cls.source={'content':base64.b64encode(cls.raw).decode(),'sha':'a'*40};cls.overlay={'content':base64.b64encode(cls.overlay_raw).decode(),'sha':'b'*40}
 def rejected_without_writes(self,source,overlay):
  with patch.object(pathlib.Path,'write_bytes')as wb,patch.object(pathlib.Path,'write_text')as wt:
   with self.assertRaises(subprocess.CalledProcessError)as error:refresh.persist_snapshot('c'*40,source,overlay)
   self.assertEqual(error.exception.returncode,2);self.assertEqual(error.exception.stdout,b'')
   self.assertNotIn(b'synthetic-fragment-value',error.exception.stderr);wb.assert_not_called();wt.assert_not_called()
 def test_origin_and_artifact_credential_fragments_refuse_before_any_snapshot_write(self):
  for field in ['origin','artifact']:
   with self.subTest(field=field):
    source=copy.deepcopy(self.source);data=json.loads(self.raw)
    url='https://example.org/proof#access_token=synthetic-fragment-value'
    if field=='origin':data['claims'][0]['origin']['source_url']=url
    else:data['claims'][0]['accepted_artifacts'][0]['url']=url
    source['content']=base64.b64encode(json.dumps(data).encode()).decode();self.rejected_without_writes(source,self.overlay)
 def test_subjective_overlay_fragment_refuses_before_claim_or_overlay_snapshot_write(self):
  overlay=copy.deepcopy(self.overlay);data=json.loads(self.overlay_raw);data['entries'][0]['source_url']='https://example.org/proof#/route?api_key=synthetic-fragment-value'
  overlay['content']=base64.b64encode(json.dumps(data).encode()).decode();self.rejected_without_writes(self.source,overlay)
 def test_valid_scientific_anchors_preserve_exact_authored_bytes(self):
  with patch.object(pathlib.Path,'write_bytes')as wb,patch.object(pathlib.Path,'write_text')as wt:
   count=refresh.persist_snapshot('c'*40,self.source,self.overlay)
   self.assertEqual(count,len(json.loads(self.raw)['claims']));self.assertEqual(wb.call_count,2);self.assertEqual(wt.call_count,2)
   self.assertEqual(wb.call_args_list[0].args[0],self.raw);self.assertEqual(wb.call_args_list[1].args[0],self.overlay_raw)
 def test_retained_source_files_are_unchanged(self):
  self.assertEqual((refresh.ROOT/'dist/claims.json').read_bytes(),self.raw)
  self.assertEqual((refresh.ROOT/'dist/subjective-reuse-ranking.json').read_bytes(),self.overlay_raw)
 def test_reviewed_body_identity_mismatch_refuses_before_validation_or_writes(self):
  with patch.object(pathlib.Path,'write_bytes')as wb,patch.object(pathlib.Path,'write_text')as wt,patch.object(refresh.subprocess,'run')as validate:
   with self.assertRaisesRegex(ValueError,'Reviewed source hash mismatch'):refresh.persist_snapshot('c'*40,self.source,self.overlay,'0'*64)
   wb.assert_not_called();wt.assert_not_called();validate.assert_not_called()
if __name__=='__main__':unittest.main()
