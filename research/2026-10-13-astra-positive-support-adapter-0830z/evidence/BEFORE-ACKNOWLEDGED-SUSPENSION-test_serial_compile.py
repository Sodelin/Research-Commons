"""Bounded resource-helper contract tests using tiny Python children, not Lean."""
import contextlib
import io
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import serial_compile as subject


class ResourceControlTests(unittest.TestCase):
    def test_active_output_is_rejected_before_child_start(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);target=root/'Example.olean'
            with patch.object(subject.subprocess,'Popen') as launch:
                with self.assertRaisesRegex(ValueError,'active outputs'):
                    subject.compile_one([sys.executable,'-c','pass'],cwd=root,env=os.environ,
                        stdout=root/'stdout',stderr=root/'stderr',input_files=[str(target.with_suffix('.olean.private'))],
                        target=target,index=0,module='Example')
                launch.assert_not_called()

    def test_child_output_and_input_identity_are_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);source=root/'input';source.write_bytes(b'exact completed input')
            events=io.StringIO()
            with contextlib.redirect_stdout(events),patch.object(subject,'THRESHOLD',-1):
                code,receipt=subject.compile_one([sys.executable,'-c',
                    'import os,time;print(os.environ["MALLOC_ARENA_MAX"],flush=True);time.sleep(0.15)'],
                    cwd=root,env=os.environ,stdout=root/'stdout',stderr=root/'stderr',
                    input_files=[source],target=root/'Example.olean',index=0,module='Example')
            self.assertEqual(code,0);self.assertEqual((root/'stdout').read_text(),'1\n')
            self.assertEqual(source.read_bytes(),b'exact completed input')
            self.assertGreater(receipt['completed_advice_sweeps'],0)
            self.assertIn('INPUT_CACHE_ADVICE_BEGIN',events.getvalue())
            self.assertTrue(receipt['sampler_pauses_during_advice'])

    def test_helper_failure_terminates_its_child(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);children=[];real_launch=subject.subprocess.Popen
            def launch(*args,**kwargs):
                child=real_launch(*args,**kwargs);children.append(child);return child
            with contextlib.redirect_stdout(io.StringIO()),patch.object(subject,'THRESHOLD',-1),\
                 patch.object(subject.subprocess,'Popen',side_effect=launch):
                with self.assertRaises(FileNotFoundError):
                    subject.compile_one([sys.executable,'-c','import time;time.sleep(30)'],
                        cwd=root,env=os.environ,stdout=root/'stdout',stderr=root/'stderr',
                        input_files=[root/'missing'],target=root/'Example.olean',index=0,module='Example')
            self.assertEqual(len(children),1);self.assertIsNotNone(children[0].poll())
            self.assertTrue((root/'stdout').exists());self.assertTrue((root/'stderr').exists())

    def test_broken_resource_logging_still_terminates_child(self):
        class BrokenAfterPolicy(io.StringIO):
            broken=False
            def write(self,text):
                if self.broken:raise BrokenPipeError('test outer log closed')
                result=super().write(text)
                if '\n' in text:self.broken=True
                return result
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);children=[];real_launch=subject.subprocess.Popen
            def launch(*args,**kwargs):
                child=real_launch(*args,**kwargs);children.append(child);return child
            with contextlib.redirect_stdout(BrokenAfterPolicy()),patch.object(subject,'THRESHOLD',-1),\
                 patch.object(subject.subprocess,'Popen',side_effect=launch):
                with self.assertRaisesRegex(BrokenPipeError,'test outer log closed'):
                    subject.compile_one([sys.executable,'-c','import time;time.sleep(30)'],
                        cwd=root,env=os.environ,stdout=root/'stdout',stderr=root/'stderr',
                        input_files=[],target=root/'Example.olean',index=0,module='Example')
            self.assertEqual(len(children),1);self.assertIsNotNone(children[0].poll())


    def test_between_compiler_advice_runs_only_after_child_exit(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);source=root/'input';source.write_bytes(b'unchanged')
            children=[];calls=[];real_launch=subject.subprocess.Popen
            def launch(*args,**kwargs):
                child=real_launch(*args,**kwargs);children.append(child);return child
            def advise(*args):
                self.assertEqual(len(children),1)
                self.assertIsNotNone(children[0].poll())
                calls.append(args)
            with contextlib.redirect_stdout(io.StringIO()),patch.object(subject,'THRESHOLD',10**30),\
                 patch.object(subject,'AFTER_EXIT_THRESHOLD',-1),\
                 patch.object(subject.subprocess,'Popen',side_effect=launch),\
                 patch.object(subject.os,'posix_fadvise',side_effect=advise):
                code,receipt=subject.compile_one([sys.executable,'-c','pass'],cwd=root,env=os.environ,
                    stdout=root/'stdout',stderr=root/'stderr',input_files=[source],
                    target=root/'Example.olean',index=0,module='Example')
            self.assertEqual(code,0);self.assertEqual(len(calls),1)
            self.assertEqual(source.read_bytes(),b'unchanged')
            self.assertTrue(receipt['after_exit_advice'])
            self.assertEqual(receipt['completed_advice_sweeps'],0)


if __name__=='__main__':unittest.main(verbosity=2)
