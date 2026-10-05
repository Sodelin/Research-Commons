import pathlib,tempfile,unittest,json
from unittest.mock import MagicMock,patch
import run_fixed_leading as r
class FixedTests(unittest.TestCase):
    def test_exact_conditional_delta(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d);(p/'LOCAL-EXAMPLE-ADMISSION.json').write_bytes((r.ROOT/'LOCAL-EXAMPLE-ADMISSION.json').read_bytes())
            proc=MagicMock();proc.pid=123;proc.wait.return_value=0;proc.poll.return_value=0
            with patch.object(r,'ROOT',p),patch.object(r.subprocess,'Popen',return_value=proc):r.run('test','A00',9101,20000,50000,2,1,600)
            folder=p/'runs'/'test';ctl=(folder/'control.ctl').read_text();t=json.loads((folder/'TERMINAL.json').read_text())
            self.assertIn('(((H, L), C), K);',ctl)
            self.assertRegex(ctl,r'speciestree\s*=\s*0\n')
            for marker in ['thetaprior = gamma 2 2000','tauprior = gamma 2 1000','phase =   1  1  1  1','cleandata = 0']:
                self.assertIn(marker,ctl)
            self.assertEqual(t['conditional_topology'],'(((H,L),C),K);');self.assertTrue(t['inputs_stable'])
    def test_wrong_analysis_rejected(self):
        with self.assertRaises(ValueError):r.run('test','A01',1,1,1,1,1,1)
if __name__=='__main__':unittest.main()
