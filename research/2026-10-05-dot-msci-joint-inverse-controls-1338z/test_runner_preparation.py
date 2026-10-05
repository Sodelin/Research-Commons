import tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import seq_engine as e
import sequential_runner as r
import prepare_controls as p
from test_state_recovery import setup
class Tests(unittest.TestCase):
    def test_source_manifest_refusal(self):
        with tempfile.TemporaryDirectory() as td:
            file=Path(td)/'pins.json';file.write_text('{}')
            with self.assertRaises(ValueError):r.authenticate(file,'0'*64)
    def test_receipt_failure_has_terminal(self):
        real=r.prior.dump_new
        def inject(path,obj):
            if Path(path).name=='BEFORE.json':raise OSError('tiny initial write fault')
            return real(path,obj)
        with tempfile.TemporaryDirectory() as td:
            req,h,q=setup(td);manifest=Path(td)/'pins.json';manifest.write_bytes(e.canonical({name:e.sha((r.BASE/name).read_bytes()) for name in r.FILES}))
            with patch.object(r.prior,'dump_new',side_effect=inject),patch.object(r.prior,'stage') as stage:out=r.run(req,h,Path(td)/'attempt',manifest,e.sha(manifest.read_bytes()))
            stage.assert_not_called();self.assertEqual(out['certificate_status'],'NO_COMPLETED_CERTIFICATE');self.assertEqual(out['failure']['type'],'OSError')
    def test_preparation_never_evaluates_forward_or_AD(self):
        with tempfile.TemporaryDirectory() as td,patch('interval_ad.evaluate') as AD,patch('interval_math.forward.evaluate') as forward:
            identity=p.prepare(Path(td)/'prepared');manifest=e.read_json(Path(td)/'prepared/CONTROL-MANIFEST.json',identity)
            AD.assert_not_called();forward.assert_not_called();self.assertEqual(len(manifest['controls']),8)
            for entry in manifest['controls']:e.read_request(Path(td)/'prepared'/entry['request'],entry['sha256'])
if __name__=='__main__':unittest.main()
