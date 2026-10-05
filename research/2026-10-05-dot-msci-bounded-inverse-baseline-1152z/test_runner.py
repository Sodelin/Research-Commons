import hashlib,json,subprocess,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import bounded_runner as r
import fixture_requests as f
import filter_core as c

class Tests(unittest.TestCase):
    def test_small_timeout_cleanup(self):
        with tempfile.TemporaryDirectory() as td:
            out=r.stage([sys.executable,'-c','import time; time.sleep(3)'],Path(td),'tiny',r.load_watchdog(),wall=.1)
            self.assertEqual(out['status'],'RESOURCE_TIME_LIMIT');self.assertTrue(out['direct_child_reaped']);self.assertTrue(out['process_group_cleanup_performed']);self.assertTrue((Path(td)/'tiny-TERMINAL.json').exists())
    def test_small_timeout_recovers_committed_root(self):
        import check_cover
        with tempfile.TemporaryDirectory() as td:
            folder=Path(td);request=folder/'request.json';identity=f.write_request(request,f.request_dict(max_evaluations=0));states=folder/'states'
            script="import sys,time; from pathlib import Path; import filter_core as c; q=c.read_request(sys.argv[1],sys.argv[2]); c.run_filter(q,Path(sys.argv[3])); time.sleep(3)"
            out=r.stage([sys.executable,'-c',script,str(request),identity,str(states)],folder,'tiny-root',r.load_watchdog(),wall=.5)
            self.assertEqual(out['status'],'RESOURCE_TIME_LIMIT')
            result=check_cover.certify_or_recover(request,identity,states,r.digest(c.__file__),normal=False)
            self.assertEqual(result['status'],'RECOVERED_UNKNOWN');self.assertEqual(result['mode'],'recovered_validated_checkpoint');self.assertEqual(len(result['retained_cover']),1)
    def test_exception_after_spawn_cleans_group(self):
        watchdog=r.load_watchdog();real=watchdog.terminate_group;seen=[]
        def cleanup(proc):seen.append(proc);real(proc)
        with tempfile.TemporaryDirectory() as td,patch.object(watchdog,'monitor',side_effect=OSError('tiny injected monitor error')),patch.object(watchdog,'terminate_group',side_effect=cleanup):
            with self.assertRaises(OSError):r.stage([sys.executable,'-c','import time; time.sleep(3)'],Path(td),'tiny',watchdog,wall=.1)
        self.assertEqual(len(seen),1);self.assertIsNotNone(seen[0].poll())
    def test_symlink_output_is_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            path=Path(td);(path/'a').write_text('x');(path/'link').symlink_to(path/'a')
            with self.assertRaises(ValueError):r.load_watchdog().tree_bytes(path)
    def test_changed_source_manifest_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'pins.json';p.write_text('{}')
            with self.assertRaises(ValueError):r.pin_sources(p,'0'*64)
            with self.assertRaises(ValueError):r.pin_sources(p,r.digest(p))
    def test_before_receipt_failure_is_terminal(self):
        real=r.dump_new
        def fail_before(path,obj):
            if Path(path).name=='BEFORE.json':raise OSError('tiny injected initial receipt failure')
            return real(path,obj)
        with tempfile.TemporaryDirectory() as td:
            folder=Path(td);request=folder/'request.json';identity=f.write_request(request,f.request_dict(max_evaluations=0));manifest=r.BASE/'SOURCE-PINS.json'
            with patch.object(r,'dump_new',side_effect=fail_before),patch.object(r,'stage') as stage:
                result=r.run(request,identity,folder/'attempt',manifest,r.digest(manifest))
            stage.assert_not_called();self.assertEqual(result['certificate_status'],'NO_COMPLETED_CERTIFICATE');self.assertEqual(result['failure']['type'],'OSError');self.assertTrue((folder/'attempt'/'TERMINAL.json').exists())
    def test_broad_radius_exact(self):
        d=f.request_dict(kind='broad');self.assertEqual(c.radius(c.parse_box(d['box'])),c.F(209,40))

if __name__=='__main__':unittest.main()
