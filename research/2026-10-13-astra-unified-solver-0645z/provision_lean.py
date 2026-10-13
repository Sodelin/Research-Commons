#!/usr/bin/env python3
"""Provision the historical official Lean compiler into new cloud scratch.

Requires zstd/tar. Run under guard.py. Public downloads; no global installation.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import os
import tarfile
import urllib.request

URL = 'https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst'
ARCHIVE_SHA = '890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235'
BINARY_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'


def main():
    dest = Path(sys.argv[1]).resolve()
    resume = len(sys.argv) == 3 and sys.argv[2] == '--resume-authenticated-archive'
    dest.mkdir(parents=True, exist_ok=resume)
    archive = dest/'lean.tar.zst'
    digest = hashlib.sha256()
    size = 0
    if not resume:
        with urllib.request.urlopen(URL, timeout=30) as response, archive.open('xb') as out:
            while data := response.read(1024*1024):
                size += len(data)
                if size > 600_000_000:
                    raise ValueError('archive exceeded authenticated size cap')
                out.write(data)
    size = 0
    with archive.open('rb') as downloaded:
        while data := downloaded.read(1024*1024):
            size += len(data)
            digest.update(data)
    if size != 570405234 or digest.hexdigest() != ARCHIVE_SHA:
        raise ValueError('official Lean archive identity mismatch')
    # Authenticated official archive; keep it alongside the extracted evidence.
    # The first ordinary tar extraction hit the conservative 4-GiB cgroup
    # guard on dirty file cache. Preserve that receipt and archive. Release
    # only our own completed output's file-cache pages as extraction proceeds;
    # no system-wide cache setting, source deletion, or memory-cap increase.
    process = subprocess.Popen(['zstd', '-dc', str(archive)], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=process.stdout, mode='r|') as tar:
            for member in tar:
                tar.extract(member, dest, filter='data')
                if member.isfile():
                    with (dest/member.name).open('rb') as completed:
                        os.fsync(completed.fileno())
                        os.posix_fadvise(completed.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
        if process.wait(timeout=10) != 0:
            raise RuntimeError('zstd extraction failed')
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    binary = dest/'lean-4.33.1-linux/bin/lean'
    got = hashlib.sha256(binary.read_bytes()).hexdigest()
    if got != BINARY_SHA:
        raise ValueError('historically accepted Lean binary identity mismatch')
    version = subprocess.check_output([str(binary), '--version'], text=True)
    result = dict(url=URL, archive_bytes=size, archive_sha256=ARCHIVE_SHA,
                  compiler_sha256=got, version=version, compiler=str(binary),
                  historical_compiler_identity_match=True, fresh_component_compilation=False)
    (dest/'PROVISIONING.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
