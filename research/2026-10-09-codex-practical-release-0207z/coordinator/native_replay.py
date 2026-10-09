#!/usr/bin/env python3
"""Reproduce pinned native diagnostics in fresh scratch; provisioning uses network.

Requires Python >=3.11, Linux x86_64, C/linker tools and public network access.
Does not change the producer. Downloads/install/build outputs stay in scratch.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import sys
import time
from types import ModuleType

ROOT = Path(__file__).resolve().parents[3]
BASELINE = ROOT / 'research/2026-10-08-codex-integration-0825z/practical'
EXPECTED = {
    'provision_pinned.py': '13430a76cdfc3a8640b9f02da06b4891f8e7be82ec0234d7796acf169a8ccb7c',
    'build_and_compare.py': '3c524eb25aad0f84abec88d14abab011b1c6ab870696ab6aac23fa6ca3f83139',
}


def captured(name):
    path = BASELINE / name
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != EXPECTED[name]:
        raise ValueError('Inherited helper identity mismatch: ' + name)
    module = ModuleType('release_' + path.stem)
    module.__file__ = str(path)
    exec(compile(data, str(path), 'exec'), module.__dict__)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scratch', type=Path, required=True, help='New scratch directory.')
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    if scratch.is_relative_to(ROOT):
        raise ValueError('Choose scratch outside the repository; no toolchains are packaged.')
    scratch.mkdir(parents=True, exist_ok=False)
    packet = scratch / 'packet'
    packet.mkdir()
    (packet / 'logs').mkdir()
    # Scratch-only symlink points to already public frozen source.
    (packet / 'recovered').symlink_to(BASELINE / 'recovered', target_is_directory=True)
    shutil.copyfile(BASELINE / 'RECOVERY.json', packet / 'RECOVERY.json')
    result = {'schema': 'fresh_native_replay_v1', 'fresh_execution': True,
              'inherited_helpers': EXPECTED,
              'network_provisioning': True, 'cargo_locked_offline_after_provisioning': True,
              'native_is_post_checker_diagnostic': True,
              'producer_replacement_or_acceleration': False,
              'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
    started = time.monotonic()
    # Public network egress in hosted environments can require system proxies.
    # Preserve transport configuration only during provisioning; never log it.
    transport_names = {'HTTPS_PROXY', 'HTTP_PROXY', 'ALL_PROXY', 'NO_PROXY',
                       'https_proxy', 'http_proxy', 'all_proxy', 'no_proxy',
                       'SSL_CERT_FILE', 'SSL_CERT_DIR', 'REQUESTS_CA_BUNDLE'}
    transport = {key: value for key, value in os.environ.items() if key in transport_names}
    # Child tools never receive application credentials or the GitHub token.
    os.environ.clear()
    os.environ.update(PATH=os.defpath, LANG='C.UTF-8', PYTHONDONTWRITEBYTECODE='1',
                      PYTHONNOUSERSITE='1', PYTHONHASHSEED='0')
    try:
        provision = captured('provision_pinned.py')
        provision.BASE = scratch / 'runtime'
        provision.BASE.mkdir()
        provision.PACKET = packet
        os.environ.update(transport)
        provision.main()
        for key in transport:
            os.environ.pop(key, None)
        build = captured('build_and_compare.py')
        build.PACKET = packet
        build.SCRATCH = provision.BASE
        build.RECOVERED = BASELINE / 'recovered'
        build.main()
        summary = json.loads((packet / 'signed-differential/RESULT.json').read_text())
        result.update(status='PASS', differential=summary,
                      native_binary=str(build.SCRATCH / 'signed-target/release/signed-nine-probe'))
    except Exception as error:
        result.update(status='FAILED', error_type=type(error).__name__, error=str(error))
        raise
    finally:
        result['wall_seconds'] = time.monotonic() - started
        result['ended_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        (packet / 'REPLAY-RESULT.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': result['status'], 'packet': str(packet),
                      'native_binary': result['native_binary']}))


if __name__ == '__main__':
    main()
