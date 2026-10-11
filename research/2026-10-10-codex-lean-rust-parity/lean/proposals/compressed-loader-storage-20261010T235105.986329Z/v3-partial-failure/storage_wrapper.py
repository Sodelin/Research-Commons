#!/usr/bin/env python3
"""Prospective storage adapter. Importing this source launches no process.

The canonical builder is not edited. Compiler argv/cwd, kernel options, source
and import checks, native library checks, caps and audit predicates remain in
the invoke derivative. Its logging environment omits LD_DEBUG_OUTPUT: glibc
trace and Lean diagnostics share a bounded, lossless gzip stderr stream.
"""
from pathlib import Path
import gzip
import hashlib
import json
import os
import re
import selectors
import shutil
import subprocess
import time

CORE_SHA256 = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'
RAW_LIMIT_BYTES = 32 * 1024 * 1024
GZIP_LIMIT_BYTES = 1024 * 1024
READ_BYTES = 64 * 1024
TAIL_RESERVE_BYTES = 256 * 1024


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for data in iter(lambda: f.read(READ_BYTES), b''):
            h.update(data)
    return h.hexdigest()


class CaptureLimit(RuntimeError):
    pass


class LimitedEncodedWriter:
    """Enforce the encoded bound before every physical write."""
    def __init__(self, out, limit):
        self.out, self.limit, self.count = out, limit, 0

    def write(self, data):
        if self.count + len(data) > self.limit:
            raise CaptureLimit('gzip byte limit before physical write')
        written = self.out.write(data)
        if written != len(data):
            raise OSError('short capture write')
        self.count += written
        return written

    def flush(self):
        self.out.flush()


def inspect_capture(path, expected_raw_sha256, expected_raw_bytes,
                    raw_limit=RAW_LIMIT_BYTES, gzip_limit=GZIP_LIMIT_BYTES):
    """Authenticate the complete decoded stream before interpreting its text."""
    path = Path(path)
    if path.stat().st_size > gzip_limit:
        raise CaptureLimit('encoded input exceeds bound')
    encoded_before = file_sha(path)
    h, count, chunks = hashlib.sha256(), 0, []
    with gzip.open(path, 'rb') as source:
        for data in iter(lambda: source.read(READ_BYTES), b''):
            if count + len(data) > raw_limit:
                raise CaptureLimit('decoded input exceeds bound')
            count += len(data)
            h.update(data)
            chunks.append(data)
    if count != expected_raw_bytes or h.hexdigest() != expected_raw_sha256:
        raise ValueError('decoded stream byte identity mismatch')
    # This is the same UTF-8/errors=replace conversion used by Path.read_text.
    # Full text inspection also catches ASCII sorryAx spanning capture chunks.
    text = b''.join(chunks).decode('utf-8', errors='replace')
    if file_sha(path) != encoded_before:
        raise ValueError('encoded stream changed during inspection')
    native_used = sorted({str(Path(x).resolve())
                          for x in re.findall(r'calling init:\s*(/[^\s]+)', text)})
    return {'text': text, 'native_used': native_used, 'eof': True,
            'raw_sha256': h.hexdigest(), 'raw_bytes': count,
            'gzip_sha256': encoded_before, 'gzip_bytes': path.stat().st_size,
            'encoding': 'gzip', 'complete': True, 'truncated': False}


def preserve_partial_failure(destination, error, observed_hash, observed_count,
                             supplied_hash, supplied_count, observed_eof=False,
                             exit_code=None):
    """Best-effort failure sidecar; prefix identities never establish completeness."""
    destination = Path(destination)
    record = {
        'status':'FAILED_PARTIAL_CAPTURE_NOT_VERIFIED',
        'complete':False, 'truncated':True, 'eof':False,
        'observed_pipe_eof':observed_eof, 'exit_code':exit_code,
        'exception_type':type(error).__name__, 'reason':str(error),
        'gzip_path':str(destination), 'gzip_integrity_verified':False,
        'observed_input_bytes':observed_count,
        'observed_input_sha256':observed_hash.hexdigest(),
        'chunks_successfully_supplied_to_gzip_bytes':supplied_count,
        'chunks_successfully_supplied_to_gzip_sha256':supplied_hash.hexdigest(),
        'identity_qualification':'Observed/supplied prefixes do not bind a complete decoded stream.'}
    try:
        if destination.is_file():
            record.update(preserved_gzip_prefix_bytes=destination.stat().st_size,
                          preserved_gzip_prefix_sha256=file_sha(destination))
        sidecar = destination.with_name(destination.name+'.FAILED-PARTIAL.json')
        with sidecar.open('x') as out:
            json.dump(record,out,indent=2)
            out.write('\n')
    except Exception as preservation_error:
        # Preserve the original failure and any existing prefix on ENOSPC too.
        error.add_note('Partial sidecar could not be written: '+repr(preservation_error))
    return record


def capture_saved_file(source, destination, raw_limit=RAW_LIMIT_BYTES,
                       gzip_limit=GZIP_LIMIT_BYTES):
    """Byte-only trial entrypoint; refuses overwriting any destination."""
    source, destination = Path(source), Path(destination)
    h, count = hashlib.sha256(), 0
    observed_hash, observed_count, created = hashlib.sha256(), 0, False
    try:
        with destination.open('xb') as out:
            created = True
            bounded = LimitedEncodedWriter(out, gzip_limit)
            with gzip.GzipFile(filename='', mode='wb', fileobj=bounded,
                               compresslevel=6, mtime=0) as encoded:
                with source.open('rb') as raw:
                    for data in iter(lambda: raw.read(READ_BYTES), b''):
                        observed_hash.update(data)
                        observed_count += len(data)
                        if count + len(data) > raw_limit:
                            raise CaptureLimit('saved raw byte limit')
                        encoded.write(data)
                        h.update(data)
                        count += len(data)
        result = inspect_capture(destination, h.hexdigest(), count,
                                 raw_limit, gzip_limit)
        result.pop('text')
        result['source_path'] = str(source)
        result['gzip_path'] = str(destination)
        result['source_unchanged'] = file_sha(source) == h.hexdigest()
        if not result['source_unchanged']:
            raise ValueError('saved source changed during trial')
        return result
    except BaseException as error:
        if created:
            preserve_partial_failure(destination,error,observed_hash,observed_count,h,count)
        raise


def capture_process(command, cwd, env, stdout, destination, timeout):
    """One child, one bounded reader; no session, thread or global hook."""
    destination = Path(destination)
    h, count, reason, eof, code = hashlib.sha256(), 0, None, False, None
    observed_hash, observed_count, created = hashlib.sha256(), 0, False
    proc, failure = None, None
    selector = selectors.DefaultSelector()
    started = time.monotonic()
    try:
        with destination.open('xb') as out:
            created = True
            bounded = LimitedEncodedWriter(out, GZIP_LIMIT_BYTES)
            with gzip.GzipFile(filename='', mode='wb', fileobj=bounded,
                               compresslevel=6, mtime=0) as encoded:
                proc = subprocess.Popen(command, cwd=cwd, env=env,
                                        stdout=stdout, stderr=subprocess.PIPE)
                os.set_blocking(proc.stderr.fileno(), False)
                selector.register(proc.stderr, selectors.EVENT_READ)
                while not eof:
                    if reason is None and time.monotonic() - started >= timeout:
                        reason = 'compiler timeout'
                        proc.kill()
                    events = selector.select(0.05)
                    for key, _ in events:
                        data = os.read(key.fd, READ_BYTES)
                        if not data:
                            eof = True
                            selector.unregister(proc.stderr)
                            break
                        observed_hash.update(data)
                        observed_count += len(data)
                        if count + len(data) > RAW_LIMIT_BYTES:
                            raise CaptureLimit('decoded hard limit while draining')
                        encoded.write(data)
                        h.update(data)
                        count += len(data)
                        if reason is None and (
                            count >= RAW_LIMIT_BYTES - TAIL_RESERVE_BYTES or
                            bounded.count >= GZIP_LIMIT_BYTES - TAIL_RESERVE_BYTES
                        ):
                            reason = 'capture soft limit; terminate and preserve pipe tail'
                            proc.kill()
                    if reason is not None and time.monotonic() - started > timeout + 5:
                        raise CaptureLimit('stderr pipe did not reach EOF after termination')
                try:
                    code = proc.wait(timeout=max(0.001, timeout - (time.monotonic()-started)))
                except subprocess.TimeoutExpired:
                    reason = reason or 'compiler timeout after stderr EOF'
                    proc.kill()
                    proc.wait()
                    code = 124
                if reason == 'compiler timeout':
                    code = 124
    except BaseException as error:
        failure = error
        raise
    finally:
        # The unchanged outer guard owns the group. Every local error reaps
        # the compiler leader before publishing an explicitly partial sidecar.
        try:
            if proc is not None:
                if proc.poll() is None:
                    try:
                        proc.kill()
                    except ProcessLookupError:
                        pass
                proc.wait()
        except BaseException as cleanup_error:
            if failure is None:
                failure = cleanup_error
                raise
            failure.add_note('Leader cleanup error: '+repr(cleanup_error))
        finally:
            try:
                if proc is not None and proc.stderr is not None:
                    proc.stderr.close()
            finally:
                selector.close()
                if failure is not None and created:
                    preserve_partial_failure(destination,failure,observed_hash,observed_count,
                                             h,count,eof,proc.returncode if proc else None)
    try:
        result = inspect_capture(destination, h.hexdigest(), count)
    except BaseException as error:
        preserve_partial_failure(destination,error,observed_hash,observed_count,h,count,eof,code)
        raise
    result.update(gzip_path=str(destination), reason=reason,
                  exit_code=code, eof=eof, complete=eof, truncated=False)
    return result


def native_evidence_known(captured, native_used, native_runtime):
    """Require authenticated initialized-library evidence, not an empty file."""
    return (captured['complete'] and not captured['truncated'] and
            bool(native_used) and all(p in native_runtime for p in native_used))


def make_builder_class(parent, core, policy):
    """Bind a reviewed namespace builder; default policy cannot execute."""
    if file_sha(core.__file__) != CORE_SHA256:
        raise ValueError('canonical core identity mismatch')
    if policy.get('raw_limit_bytes') != RAW_LIMIT_BYTES or policy.get('gzip_limit_bytes') != GZIP_LIMIT_BYTES:
        raise ValueError('capture cap identity mismatch')
    # C3 places this override below the authenticated/namespace parents and
    # above core.Builder. Their invoke before/after inventory checks therefore
    # still run through their unchanged super() calls.
    class StorageInvocation(core.Builder):
        def invoke(self, name, source, obj, imports, context, seconds, memory, kind):
            if not policy.get('runtime_authorized', False):
                raise RuntimeError('source-only storage policy cannot launch a compiler')
            self.attempt += 1
            attempt = self.run/'attempts'/f'{self.attempt:05d}-{core.safe(name)}'
            attempt.mkdir(parents=True)
            work = attempt/'work'
            work.mkdir()
            (attempt/'evidence').mkdir()
            frozen = work/(name.replace('.','/')+'.lean')
            frozen.parent.mkdir(parents=True, exist_ok=True)
            frozen.write_bytes(source.read_bytes())
            before = self.dependencies(context, imports)
            env = dict(os.environ, LEAN_PATH=':'.join(map(str,[context]+self.external)),
                       LEAN_NUM_THREADS='1', LD_DEBUG='libs')
            env.pop('LD_DEBUG_OUTPUT', None)
            output = attempt/(name.replace('.','/')+'.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            cmd = [str(self.bin/'lean'), '-j1', '-t0', '-M'+str(memory), '-Ddebug.skipKernelTC=false']
            if obj:
                cmd += ['-o', str(output)]
            cmd += [str(frozen.relative_to(work))]
            start = time.monotonic()
            with (attempt/'stdout').open('wb') as out:
                captured = capture_process(cmd, work, env, out, attempt/'stderr.raw.gz', seconds)
            stderr_text = captured.pop('text')
            native_used = captured.pop('native_used')
            core.save(attempt/'STDERR-CAPTURE.json', captured)
            after = self.dependencies(context, imports)
            native_stable = all([p.stat().st_dev,p.stat().st_ino,p.stat().st_size,p.stat().st_mtime_ns,p.stat().st_ctime_ns] == self.native_runtime[str(p)]['stat_identity'] for p in self.native_paths)
            native_known = native_evidence_known(captured, native_used, self.native_runtime)
            stable = before == after and core.sha(source) == core.sha(frozen) and native_stable and native_known
            log = (attempt/'stdout').read_text(errors='replace') + stderr_text
            code = captured['exit_code']
            passed = code == 0 and captured['reason'] is None and stable and 'sorryAx' not in log
            rec = {'status':'PASS_FRESH_KERNEL_CHECK' if passed else 'FAILED_OR_RESOURCE', 'module':name,'kind':kind,'source_sha256':core.sha(frozen),'compiler_sha256':core.BINARY,'mathlib_commit':core.MATHLIB,'command':cmd,'cap_seconds':seconds,'cap_memory_mib':memory,'exit_code':code,'elapsed_seconds':time.monotonic()-start,'source_and_imports_stable':stable,'native_runtime_digest':self.native_digest,'native_runtime_stat_stable':native_stable,'native_loader_outputs':[{'path':str(attempt/'stderr.raw.gz'),'sha256':captured['gzip_sha256'],'encoding':'gzip','raw_sha256':captured['raw_sha256'],'raw_bytes':captured['raw_bytes']}],'native_initialized_libraries':{p:self.native_runtime.get(p) for p in native_used},'native_initialized_libraries_bound':native_known,'direct_import_bindings':before,'direct_import_sha256':{m:x['sha256'] for m,x in before.items()},'direct_import_artifacts':{m:x['artifacts'] for m,x in before.items()},'stdout_sha256':core.sha(attempt/'stdout'),'stderr_sha256':captured['raw_sha256'],'stderr_storage':captured,'receipt_directory':str(attempt),'storage_wrapper_sha256':file_sha(__file__),'logging_qualification':'LD_DEBUG=libs; LD_DEBUG_OUTPUT omitted; full combined diagnostics and loader stderr preserved as gzip; decoded bytes drive original predicates'}
            if passed and obj:
                rec.update(object_sha256=core.sha(output),object_artifacts=core.artifact_bundle(output))
            rec['working_directory'] = str(work)
            rec['auxiliary_outputs'] = [{'path':str(p.relative_to(attempt)),'sha256':core.sha(p),'bytes':p.stat().st_size} for p in attempt.rglob('*.json') if p.name != 'receipt.json']
            core.save(attempt/'receipt.json', rec)
            if not passed:
                return rec, None
            if not obj:
                rec['audit_output'] = str(work/'AUDIT-RESULT.json')
            return rec, output if obj else None

        def cache_result(self, key, rec, obj):
            # Only newly compiled outputs in this run gain same-FS aliases.
            # Original authenticated prior candidates use the unchanged method.
            if not Path(obj).resolve().is_relative_to((self.run/'attempts').resolve()):
                return super().cache_result(key, rec, obj)
            destination = self.cache/key
            folder = self.cache/('.staging-'+key+'-'+str(time.time_ns()))
            folder.mkdir(exist_ok=False)
            for suffix in core.SUFFIXES:
                source = obj.with_suffix(suffix) if suffix in ['.olean','.ilean','.ir'] else Path(str(obj)+suffix[len('.olean'):])
                if source.exists():
                    # EXDEV is a refusal for NEW fresh outputs; no hidden copy.
                    os.link(source, folder/('artifact'+suffix))
            assert core.artifact_bundle(folder/'artifact.olean') == rec['object_artifacts']
            rec = {**rec, 'cached_object':str(destination/'artifact.olean'),
                   'fresh_storage_qualification':'same-FS hardlinks to immutable successful attempt outputs; no original object or receipt changed'}
            core.save(folder/'receipt.json', rec)
            if destination.exists():
                if (destination/'receipt.json').exists():
                    raise RuntimeError('Completed cache key already exists; refusing overwrite '+key)
                quarantine = self.cache/('.incomplete-'+key+'-'+str(time.time_ns()))
                destination.rename(quarantine)
                self.event(cache_key=key,status='INCOMPLETE_CACHE_PRESERVED',path=str(quarantine))
            folder.rename(destination)
            return rec
    class StorageBuilder(parent, StorageInvocation):
        pass
    expected_mro = StorageBuilder.mro()
    if expected_mro.index(parent) >= expected_mro.index(StorageInvocation):
        raise ValueError('authenticated wrapper must precede storage invocation')
    return StorageBuilder
