import os,subprocess,sys,tempfile,time,unittest
from pathlib import Path
import watchdog as w
class WatchdogTests(unittest.TestCase):
    def test_nested_aggregate(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);(p/'deep'/'nested').mkdir(parents=True)
            (p/'a').write_bytes(b'a'*13);(p/'deep'/'b').write_bytes(b'b'*17);(p/'deep'/'nested'/'c').write_bytes(b'c'*19)
            self.assertEqual(w.tree_bytes(p),49)
    def test_tiny_size_limit_preserves_files(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            code="from pathlib import Path;import time;p=Path('nested');p.mkdir();\nfor i in range(100):\n (p/'a').open('ab').write(b'x'*512);(p/'b').open('ab').write(b'y'*512);time.sleep(.01)"
            proc=subprocess.Popen([sys.executable,'-c',code],cwd=p,start_new_session=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
            try:r=w.monitor(proc,p,2,4096,receipt_reserve_bytes=1024,poll_seconds=.005)
            finally:w.terminate_group(proc)
            self.assertEqual(r['status'],'AGGREGATE_OUTPUT_LIMIT');self.assertIsNotNone(proc.poll());self.assertTrue((p/'nested'/'a').exists());self.assertTrue((p/'nested'/'b').exists());self.assertGreaterEqual(r['peak_observed_bytes_before_final_receipt'],3072);self.assertFalse(r['hard_filesystem_quota_claimed'])
    def test_short_wall_limit(self):
        with tempfile.TemporaryDirectory() as d:
            proc=subprocess.Popen([sys.executable,'-c','import time;time.sleep(10)'],cwd=d,start_new_session=True)
            try:r=w.monitor(proc,Path(d),.05,4096,receipt_reserve_bytes=1024,poll_seconds=.005)
            finally:w.terminate_group(proc)
            self.assertEqual(r['status'],'RESOURCE_TIME_LIMIT');self.assertIsNotNone(proc.poll())
    def test_success(self):
        with tempfile.TemporaryDirectory() as d:
            proc=subprocess.Popen([sys.executable,'-c',"from pathlib import Path;Path('small').write_text('done')"],cwd=d,start_new_session=True)
            r=w.monitor(proc,Path(d),2,4096,receipt_reserve_bytes=1024,poll_seconds=.005)
            self.assertEqual(r['status'],'EXECUTION_EXIT_ZERO');self.assertEqual(r['exit_code'],0);self.assertEqual((Path(d)/'small').read_text(),'done')
    def test_no_follow_symlink_directory(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);(p/'actual').mkdir();(p/'actual'/'x').write_bytes(b'x'*11);(p/'link').symlink_to('actual',target_is_directory=True)
            with self.assertRaisesRegex(ValueError,'symlink'):w.tree_bytes(p)
    def test_descendant_cleanup_after_parent_exit(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            child="import time;from pathlib import Path;\nfor i in range(1000):\n Path('heartbeat').open('ab').write(b'x');time.sleep(.01)"
            code="import subprocess,sys;from pathlib import Path;p=subprocess.Popen([sys.executable,'-c',"+repr(child)+"]);Path('childpid').write_text(str(p.pid))"
            proc=subprocess.Popen([sys.executable,'-c',code],cwd=p,start_new_session=True)
            r=w.monitor(proc,p,3,65536,receipt_reserve_bytes=1024,poll_seconds=.005)
            before=(p/'heartbeat').stat().st_size if (p/'heartbeat').exists() else 0
            time.sleep(.03)
            after=(p/'heartbeat').stat().st_size if (p/'heartbeat').exists() else 0
            self.assertEqual(before,after);self.assertEqual(r['status'],'EXECUTION_EXIT_ZERO')
if __name__=='__main__':unittest.main()
