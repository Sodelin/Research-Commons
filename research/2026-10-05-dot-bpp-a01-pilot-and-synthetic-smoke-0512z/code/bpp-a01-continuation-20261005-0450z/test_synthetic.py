import pathlib,tempfile,unittest
from unittest.mock import MagicMock,patch
import run_synthetic_control as r
class SyntheticTests(unittest.TestCase):
    def test_invalid_inference_seed(self):
        for seed in [None,0,7001,9999]:
            with self.assertRaises(ValueError):r.infer(seed)
    def test_existing_folder_preserved(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d);(p/'marker').write_text('keep')
            with self.assertRaises(FileExistsError):r.execute(p,'','--simulate',{}, {})
            self.assertEqual((p/'marker').read_text(),'keep')
    def test_reject_binary(self):
        with patch.object(r,'sha',return_value='bad'):
            with self.assertRaises(ValueError):r.execute(pathlib.Path('/unreachable'),'','--simulate',{}, {})
    def test_cleanup_terminate_race(self):
        proc=MagicMock();proc.poll.return_value=None;proc.pid=123
        with patch.object(r.os,'killpg',side_effect=ProcessLookupError):r.cleanup(proc)
        proc.wait.assert_called_once_with(timeout=5)
    def test_cleanup_kills_after_timeout(self):
        proc=MagicMock();proc.poll.return_value=None;proc.pid=123;proc.wait.side_effect=[r.subprocess.TimeoutExpired('bpp',5),-9]
        with patch.object(r.os,'killpg') as kill:r.cleanup(proc)
        self.assertEqual(kill.call_count,2);self.assertEqual(proc.wait.call_count,2)
    def test_pid_failure_cleanup_and_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d)/'attempt';proc=MagicMock();proc.pid=123;proc.poll.return_value=None
            original=pathlib.Path.write_text
            def writing(path,*args,**kwargs):
                if path.name=='PID.json':raise OSError('injected')
                return original(path,*args,**kwargs)
            with patch.object(r.subprocess,'Popen',return_value=proc),patch.object(r.os,'killpg') as kill,patch.object(pathlib.Path,'write_text',writing):
                with self.assertRaises(OSError):r.execute(p,'seed=1','--simulate',{}, {})
                kill.assert_called_once()
            self.assertIn('RUNNER_FAILURE',(p/'TERMINAL.json').read_text())
if __name__=='__main__':unittest.main()
