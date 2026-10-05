import json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import sequential_runner as r
import prepare_controls as prepare
import seq_engine as e
from test_state_recovery import setup
class Tests(unittest.TestCase):
    def test_bad_manifest_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            path=Path(td)/'pins.json';path.write_text('{}')
            with self.assertRaises(ValueError):r.authenticate(path,'0'*64)
            with self.assertRaises(ValueError):r.authenticate(path,r.prior.digest(path))
    def test_initial_receipt_failure_is_classified(self):
        real=r.prior.dump_new
        def injected(path,obj):
            if Path(path).name=='BEFORE.json':raise OSError('tiny own receipt write failure')
            return real(path,obj)
        with tempfile.TemporaryDirectory() as td:
            request,identity,q=setup(td);pins={name:e.sha((r.BASE/name).read_bytes()) for name in r.FILES};manifest=Path(td)/'pins.json';manifest.write_bytes(e.canonical(pins))
            with patch.object(r.prior,'dump_new',side_effect=injected),patch.object(r.prior,'stage') as stage:
                result=r.run(request,identity,Path(td)/'attempt',manifest,e.sha(manifest.read_bytes()))
            stage.assert_not_called();self.assertEqual(result['certificate_status'],'NO_COMPLETED_CERTIFICATE');self.assertEqual(result['failure']['type'],'OSError')
    def test_unreviewed_arithmetic_spec_refused(self):
        with tempfile.TemporaryDirectory() as td,patch('interval_math.forward.evaluate') as evaluate:
            with self.assertRaises(ValueError):prepare.prepare(Path(td)/'new','0'*64)
            evaluate.assert_not_called();self.assertFalse((Path(td)/'new').exists())
    def test_new_source_strictly_interior_and_upstream_changed(self):
        spec=e.read_json(r.BASE/'CONTROL-SPEC.json',prepare.SPEC_SHA);point={key:e.legacy.rational(value) for key,value in spec['new_arithmetic_source'].items()};box=e.legacy.parse_box(spec['physical_domain'])
        for key,(lo,hi) in zip(e.ops.PHYSICAL,box):self.assertLess(lo,point[key]);self.assertLess(point[key],hi)
        self.assertNotEqual(point['h'],e.F(1,16));self.assertNotEqual(point['h']+point['u']+point['v'],e.F(3,16));self.assertNotEqual(point['rR'],e.F(5))
if __name__=='__main__':unittest.main()
