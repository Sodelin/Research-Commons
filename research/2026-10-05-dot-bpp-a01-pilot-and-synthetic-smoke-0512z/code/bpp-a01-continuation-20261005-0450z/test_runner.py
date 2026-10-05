import importlib.util
import pathlib
import tempfile
import unittest
from unittest.mock import patch, MagicMock
BASE = pathlib.Path(__file__).resolve().parent.parent / 'bpp-sequence-pilot-20261005'
spec = importlib.util.spec_from_file_location('runner', BASE / 'run_chain_v2.py')
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
class RunnerTests(unittest.TestCase):
    def test_reject_bad_names(self):
        for name in ['../escape', '/tmp/escape', '.', '', 'a/b']:
            with self.assertRaises(ValueError): r.run(name,'A01',1,1,1,1,1,1)
    def test_reject_bounds(self):
        for edits in [{'seed':0},{'burnin':-1},{'nsample':200001},{'sampfreq':101},{'timeout':1801},{'usedata':2},{'analysis':'A11'}]:
            args=dict(name='validation-only',analysis='A01',seed=1,burnin=1,nsample=1,sampfreq=1,usedata=1,timeout=1);args.update(edits)
            with self.assertRaises(ValueError): r.run(**args)
    def test_reject_pin(self):
        with patch.object(r,'sha',return_value='wrong'):
            with self.assertRaisesRegex(ValueError,'pinned admission'): r.run('validation-only','A01',1,1,1,1,1,1)
    def test_no_overwrite(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d); (p/'runs'/'existing').mkdir(parents=True); (p/'LOCAL-EXAMPLE-ADMISSION.json').write_bytes((BASE/'LOCAL-EXAMPLE-ADMISSION.json').read_bytes())
            marker=p/'runs'/'existing'/'marker';marker.write_text('unchanged')
            with patch.object(r,'ROOT',p):
                with self.assertRaises(FileExistsError):r.run('existing','A01',1,1,1,1,1,1)
            self.assertEqual(marker.read_text(),'unchanged')
    def test_pid_write_failure_terminates_child(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d); (p/'LOCAL-EXAMPLE-ADMISSION.json').write_bytes((BASE/'LOCAL-EXAMPLE-ADMISSION.json').read_bytes())
            proc=MagicMock(); proc.pid=123456; proc.poll.return_value=None; proc.wait.return_value=-15
            original=pathlib.Path.write_text
            def writing(path, *args, **kwargs):
                if path.name == 'PID.json': raise OSError('injected PID write failure')
                return original(path,*args,**kwargs)
            with patch.object(r,'ROOT',p), patch.object(r.subprocess,'Popen',return_value=proc), patch.object(r.os,'killpg') as kill, patch.object(pathlib.Path,'write_text',writing):
                with self.assertRaisesRegex(OSError,'injected'):r.run('injected','A01',1,1,1,1,1,1)
                kill.assert_called_once_with(proc.pid,r.signal.SIGTERM)
                proc.wait.assert_called_once_with(timeout=5)
            self.assertIn('RUNNER_FAILURE',(p/'runs'/'injected'/'TERMINAL.json').read_text())
if __name__=='__main__':unittest.main()
