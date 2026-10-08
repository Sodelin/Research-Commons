"""Focused identity controls: valid stale pyc and substituted helper refusal."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import py_compile
import sys
from types import ModuleType

PACKET=Path(__file__).resolve().parent


def main():
    program=(PACKET/'pipeline.py').read_bytes()
    module=ModuleType('_loader_test_verified_cli');module.__file__=str(PACKET/'pipeline.py')
    sys.modules[module.__name__]=module
    exec(compile(program,module.__file__,'exec',dont_inherit=True),module.__dict__)
    fixture=Path('/workspace/scratch/integration-practical/loader-control')
    fixture.mkdir(exist_ok=False)
    source=fixture/'same_timestamp.py';source.write_bytes(b'value = 1\n')
    timestamp=source.stat();py_compile.compile(str(source),doraise=True)
    source.write_bytes(b'value = 2\n')
    os.utime(source,ns=(timestamp.st_atime_ns,timestamp.st_mtime_ns))
    # Establish that the cache really is valid by the old loader's policy.
    spec=importlib.util.spec_from_file_location('_test_stale_fixture',source)
    old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
    digest=hashlib.sha256(source.read_bytes()).hexdigest()
    verified=module.load('_test_verified_fixture',source,digest)
    stale_pass=old.value==1 and verified.value==2
    # Substitution fails before executing the modified buffer.
    source.write_bytes(b'value = 3\n')
    guard=False
    try:module.load('_test_substituted_fixture',source,digest)
    except ValueError:guard=True
    result={'status':'PASS' if stale_pass and guard else 'UNKNOWN',
            'old_timestamp_loader_value':old.value,'verified_single_buffer_value':verified.value,
            'stale_pyc_fixture_is_timestamp_valid':old.value==1,'verified_source_pyc_not_executed':stale_pass,
            'substituted_source_refused_before_exec':guard,
            'substituted_module_not_registered':'_test_substituted_fixture' not in sys.modules,
            'executed_source_identity':verified.__executed_source_identity__,
            'pipeline_program_sha256':hashlib.sha256(program).hexdigest(),
            'fixture_only_no_solver_or_build':True}
    (PACKET/'logs/AUTHENTICATED-LOADER-CONTROLS.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,sort_keys=True))
    if result['status']!='PASS':raise RuntimeError('loader control failure')


if __name__=='__main__':main()
