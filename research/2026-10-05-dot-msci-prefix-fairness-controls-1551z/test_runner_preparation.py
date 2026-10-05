import tempfile,sys,unittest
from pathlib import Path
from unittest.mock import patch
import global_engine as e
import bounded_runner as r
import prepare_controls as p
from test_journal import setup
class Tests(unittest.TestCase):
    def test_exact_preparation_preserves_original_domain_without_evaluation(self):
        with tempfile.TemporaryDirectory() as td,patch('interval_ad.evaluate') as ad,patch('interval_math.forward.evaluate') as forward:
            identity=p.prepare(Path(td)/'prepared');manifest=e.read_json(Path(td)/'prepared/CONTROL-MANIFEST.json',identity);ad.assert_not_called();forward.assert_not_called();self.assertEqual(len(manifest['controls']),5)
            for entry in manifest['controls']:
                request=e.read_request(Path(td)/'prepared'/entry['request'],entry['sha256']);self.assertEqual(set(request['targets'].values()),{e.F(1,20)})
    def test_small_timeout_cleanup(self):
        with tempfile.TemporaryDirectory() as td:
            out=r.stage([sys.executable,'-c','import time; time.sleep(3)'],Path(td),'tiny',r.load_watchdog(),wall=.1);self.assertEqual(out['status'],'RESOURCE_TIME_LIMIT');self.assertTrue(out['direct_child_reaped']);self.assertTrue(out['process_group_cleanup_performed'])
    def test_initial_receipt_failure_recorded(self):
        real=r.dump_new
        def bad(path,data):
            if Path(path).name=='BEFORE.json':raise OSError('tiny receipt failure')
            return real(path,data)
        with tempfile.TemporaryDirectory() as td:
            request,identity,q=setup(td);manifest=Path(td)/'pins.json';manifest.write_bytes(e.canonical({name:e.sha((r.BASE/name).read_bytes()) for name in r.FILES}))
            with patch.object(r,'dump_new',side_effect=bad),patch.object(r,'stage') as stage:
                out=r.run(request,identity,Path(td)/'attempt',manifest,e.sha(manifest.read_bytes()))
            stage.assert_not_called();self.assertEqual(out['certificate_status'],'NO_NEW_CERTIFICATE');self.assertEqual(out['failure']['type'],'OSError')
    def test_monitor_failure_after_spawn_cleans_process(self):
        watchdog=r.load_watchdog();real=watchdog.terminate_group;seen=[]
        def clean(process):seen.append(process);real(process)
        with tempfile.TemporaryDirectory() as td,patch.object(watchdog,'monitor',side_effect=OSError('tiny monitor failure')),patch.object(watchdog,'terminate_group',side_effect=clean):
            with self.assertRaises(OSError):r.stage([sys.executable,'-c','import time; time.sleep(3)'],Path(td),'tiny',watchdog,wall=.1)
        self.assertEqual(len(seen),1);self.assertIsNotNone(seen[0].poll())
if __name__=='__main__':unittest.main()

class AbruptCheckerTests(unittest.TestCase):
    def test_checker_kill_never_admits_partial_stdout(self):
        def stopped(command,attempt,label,watchdog):
            (attempt/(label+'.stdout')).write_text('{"claimed_certificate":true}')
            return {'status':'EXECUTION_EXIT_ZERO' if label=='producer' else 'RESOURCE_TIME_LIMIT','exit_code':0 if label=='producer' else -15}
        with tempfile.TemporaryDirectory() as td:
            request,identity,q=setup(td);manifest=Path(td)/'pins.json';manifest.write_bytes(e.canonical({name:e.sha((r.BASE/name).read_bytes()) for name in r.FILES}))
            with patch.object(r,'stage',side_effect=stopped):out=r.run(request,identity,Path(td)/'attempt',manifest,e.sha(manifest.read_bytes()))
            self.assertFalse(out['checker_output_available']);self.assertEqual(out['certificate_status'],'NO_NEW_CERTIFICATE')
