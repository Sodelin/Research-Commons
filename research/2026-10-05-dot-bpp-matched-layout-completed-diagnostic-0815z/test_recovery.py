import json,pathlib,tempfile,unittest
from unittest.mock import MagicMock,patch
import run_recovery as r
class RunnerTests(unittest.TestCase):
    def test_simulation_profile_and_nested_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            base=pathlib.Path(d);proc=MagicMock();proc.pid=123;proc.returncode=0
            def monitor(proc,folder,wall,limit):
                self.assertEqual((wall,limit),(60,268435456));(folder/'nested').mkdir();(folder/'nested/test.txt').write_text('mock');return {'status':'EXECUTION_EXIT_ZERO','exit_code':0}
            with patch.object(r,'BASE',base),patch.object(r.subprocess,'Popen',return_value=proc),patch.object(r.watchdog,'monitor',side_effect=monitor):r.simulate()
            t=json.loads((base/'runs/simulation-seed21001/TERMINAL.json').read_text());self.assertTrue(t['inputs_stable']);self.assertIn('nested/test.txt',[x['path'] for x in t['output_inventory']])
    def test_profile_mutation_rejected(self):
        ctl=(r.DESIGN/'simulation-control.PROPOSED.ctl').read_text().replace('0.0036','0.03')
        with self.assertRaisesRegex(ValueError,'profile'):r.execute('simulation-seed21001',ctl,'--simulate',{'seed':21001},{},60)
    def test_unplanned_seed_rejected(self):
        for seed in [999,21102]:
            with self.assertRaises(ValueError):r.infer(seed)
    def test_no_overwrite(self):
        with tempfile.TemporaryDirectory() as d:
            base=pathlib.Path(d);f=base/'runs/simulation-seed21001';f.mkdir(parents=True);(f/'keep').write_text('original')
            with patch.object(r,'BASE',base):
                with self.assertRaises(FileExistsError):r.simulate()
            self.assertEqual((f/'keep').read_text(),'original')
    def test_pid_error_cleanup_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            base=pathlib.Path(d);proc=MagicMock();proc.pid=123;original=pathlib.Path.write_text
            def writing(path,*args,**kwargs):
                if path.name=='PID.json':raise OSError('injected mock write failure')
                return original(path,*args,**kwargs)
            with patch.object(r,'BASE',base),patch.object(r.subprocess,'Popen',return_value=proc),patch.object(r.watchdog,'terminate_group') as cleanup,patch.object(pathlib.Path,'write_text',writing):
                with self.assertRaises(OSError):r.simulate()
                cleanup.assert_called_once_with(proc)
            self.assertEqual(json.loads((base/'runs/simulation-seed21001/TERMINAL.json').read_text())['status'],'RUNNER_FAILURE')
    def test_symlink_error_preserves_failure_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            base=pathlib.Path(d);proc=MagicMock();proc.pid=123
            def monitor(proc,folder,*args):
                (folder/'link').symlink_to('control.ctl');raise ValueError('symlink output forbidden')
            with patch.object(r,'BASE',base),patch.object(r.subprocess,'Popen',return_value=proc),patch.object(r.watchdog,'monitor',side_effect=monitor),patch.object(r.watchdog,'terminate_group'):
                with self.assertRaises(ValueError):r.simulate()
            t=json.loads((base/'runs/simulation-seed21001/TERMINAL.json').read_text());self.assertEqual(t['status'],'RUNNER_FAILURE');self.assertIsNone(t['aggregate_final_bytes'])
    def test_changed_projector_rejected_before_gate(self):
        original=r.sha
        with patch.object(r,'sha',side_effect=lambda p:'changed' if p==r.PROJECTOR else original(p)):
            with self.assertRaisesRegex(ValueError,'dependency'):r.infer(21101)
    def test_changed_admission_rejected_before_gate(self):
        original=r.sha
        with patch.object(r,'sha',side_effect=lambda p:'changed' if p==r.ADMISSION else original(p)):
            with self.assertRaisesRegex(ValueError,'dependency'):r.infer(21101)
    def test_recovery_profile_cap_and_control(self):
        ctl=(r.DESIGN/'inference-control.PROPOSED.ctl').read_text()
        settings={'seed':21101,'burnin':20000,'nsample':5000,'sampfreq':20,'usedata':1}
        projected=r.BASE/'runs/projected-seed21001'
        inputs={'alignment':('matched-synthetic.txt',projected/'matched-synthetic.txt'),'map':('matched-synthetic.Imap.txt',projected/'matched-synthetic.Imap.txt')}
        with tempfile.TemporaryDirectory() as d:
            base=pathlib.Path(d);proc=MagicMock();proc.pid=123
            def monitor(proc,folder,wall,limit):
                self.assertEqual((wall,limit),(1800,268435456))
                self.assertEqual((folder/'control.ctl').read_text(),ctl)
                return {'status':'EXECUTION_EXIT_ZERO','exit_code':0}
            with patch.object(r,'BASE',base),patch.object(r.subprocess,'Popen',return_value=proc),patch.object(r.watchdog,'monitor',side_effect=monitor):
                t=r.execute('A00-matched-recovery-seed21101',ctl,'--cfile',settings,inputs,1800)
            self.assertEqual(t['wall_limit_seconds'],1800)
            self.assertEqual(t['input_hashes_before']['control'],'e653b2a121d85d5cde534de9d18373319e9a7459879ddccedcfc660d18485098')
            with patch.object(r,'BASE',base):
                with self.assertRaises(FileExistsError):r.execute('A00-matched-recovery-seed21101',ctl,'--cfile',settings,inputs,1800)
        for wall in [600,3600]:
            with self.assertRaises(ValueError):r.execute('A00-matched-recovery-seed21101',ctl,'--cfile',settings,inputs,wall)
if __name__=='__main__':unittest.main()
