import pathlib,tempfile,unittest,json
from unittest.mock import MagicMock,patch
import run_instrumented as r
class RunnerTests(unittest.TestCase):
    def test_exact_delta_and_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d);(p/'LOCAL-EXAMPLE-ADMISSION.json').write_bytes((r.ROOT/'LOCAL-EXAMPLE-ADMISSION.json').read_bytes())
            proc=MagicMock();proc.pid=123;proc.returncode=0;proc.poll.return_value=0
            observed={'exit_code':0,'status':'EXECUTION_EXIT_ZERO'}
            def watch(proc,folder,*args):
                (folder/'nested').mkdir();(folder/'nested/evidence.txt').write_text('small mocked output');return observed
            with patch.object(r,'ROOT',p),patch.object(r.subprocess,'Popen',return_value=proc) as popen,patch.object(r.watchdog,'monitor',side_effect=watch):
                r.run('mock','A00',10101,20000,5000,20,1,600)
            ctl=(p/'runs/mock/control.ctl').read_text();t=json.loads((p/'runs/mock/TERMINAL.json').read_text())
            for text in ['(((H, L), C), K);','thetaprior = gamma 2 2000','tauprior = gamma 2 1000','phase =   1  1  1  1']:self.assertIn(text,ctl)
            self.assertRegex(ctl,r'print\s*=\s*1 0 0 1\n');self.assertEqual(popen.call_args.args[0][-3:],['--theta_mode','3','--theta-showeps']);self.assertTrue(t['inputs_stable']);self.assertIn('watchdog',t['input_hashes_before']);self.assertLess(t['aggregate_final_bytes'],256*1024**2);self.assertIn('nested/evidence.txt',[x['path'] for x in t['output_inventory']])
    def test_reject_unplanned_budget(self):
        with self.assertRaises(ValueError):r.run('no','A00',10101,20000,5001,20,1,600)
    def test_pid_failure_cleans_up(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d);(p/'LOCAL-EXAMPLE-ADMISSION.json').write_bytes((r.ROOT/'LOCAL-EXAMPLE-ADMISSION.json').read_bytes())
            proc=MagicMock();proc.pid=123;original=pathlib.Path.write_text
            def writing(path,*args,**kwargs):
                if path.name=='PID.json':raise OSError('injected small test')
                return original(path,*args,**kwargs)
            with patch.object(r,'ROOT',p),patch.object(r.subprocess,'Popen',return_value=proc),patch.object(r.watchdog,'terminate_group') as cleanup,patch.object(pathlib.Path,'write_text',writing):
                with self.assertRaises(OSError):r.run('mock','A00',10101,20000,5000,20,1,600)
                cleanup.assert_called_once_with(proc)
            self.assertIn('RUNNER_FAILURE',(p/'runs/mock/TERMINAL.json').read_text())
if __name__=='__main__':unittest.main()
