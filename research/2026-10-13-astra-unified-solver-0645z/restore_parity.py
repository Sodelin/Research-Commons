#!/usr/bin/env python3
"""Recover an immutable public Rust core; never checkout or overwrite originals.

Run under guard.py. Fetch the immutable public commit beforehand if absent:
  git fetch origin 4e556c4ae6225d18fabf30bc7d3347a468749ebc
This script reads Git objects and authenticated public packets only. It does not
download dependencies, execute recovered code, or modify the existing checkout.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
COMMIT = '4e556c4ae6225d18fabf30bc7d3347a468749ebc'
PARITY = 'research/2026-10-10-codex-lean-rust-parity/rust'
DECODER = PARITY+'/proposals/canonical-snapshot-decoder-20261011T0905Z'
PACKET = DECODER+'/COMPLETE-SOURCE-EXECUTION-AND-QC.json'
PACKET_SHA = 'fc855b7672a55b585c48b81a1cd45bfa5e52d2b8e412673edc03303254aeef86'
SERIAL = PARITY+'/proposals/serial-full-history-control-20261011T0715Z/serial_early_late_history_tests.rs'
PREFIX = PARITY+'/proposals/selected-prefix-record-20261011T0034Z/source_selected_prefix.rs'
DEPENDENCIES = ['research/2026-10-07-rust-count-pilot',
                'research/2026-10-08-cloud-rust-interval-root-0000z',
                'research/2026-10-08-cloud-rust-signed-nine-0008z']


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    # Limit Git's per-command mmap windows as well as the enclosing process
    # resource cap. Do not change repository/global configuration.
    result = subprocess.run(['git', '-c', 'core.packedGitLimit=64m',
                             '-c', 'core.packedGitWindowSize=16m', *args], cwd=ROOT,
                            capture_output=True, timeout=20)
    if result.returncode:
        raise ValueError('Git object read failed: '+result.stderr.decode(errors='replace'))
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.manifest.exists():
        raise ValueError('restore destinations must be absent')
    packet_bytes = (ROOT/PACKET).read_bytes()
    if sha(packet_bytes) != PACKET_SHA:
        raise ValueError('decoder evidence packet identity changed')
    packet = json.loads(packet_bytes)
    artifacts = {}
    for row in packet['artifacts']:
        raw = row['content_utf8'].encode()
        if len(raw) != row['bytes'] or sha(raw) != row['sha256']:
            raise ValueError('embedded decoder artifact authentication failed')
        artifacts[row['path']] = raw
    config = json.loads(next(raw for path, raw in artifacts.items()
                             if path.endswith('guard/EXECUTION-CONFIG.json')))
    originals = [row for row in config['input_pins']
                 if row['path'].startswith('/workspace/Research-Commons/') and '/rust/' in row['path']]
    expected = {row['path'].removeprefix('/workspace/Research-Commons/'): row for row in originals}
    source_paths = set(expected)
    trees = [PARITY+'/src', *(dep+'/src' for dep in DEPENDENCIES)]
    for path in git('ls-tree', '-r', '--name-only', COMMIT, *trees).decode().splitlines():
        if path.endswith('.rs'):
            source_paths.add(path)
    for crate in [PARITY, *DEPENDENCIES]:
        source_paths.update([crate+'/Cargo.toml', crate+'/Cargo.lock'])
    source_paths.add(PARITY+'/tests/source_population.rs')
    contents, manifest = {}, []
    for path in sorted(source_paths):
        raw = git('show', COMMIT+':'+path)
        pin = expected.get(path)
        if pin and (len(raw) != pin['bytes'] or sha(raw) != pin['sha256']):
            raise ValueError('historical decoder parent mismatch: '+path)
        if len(raw) > 1024**2:
            raise ValueError('per-file restore cap')
        contents[path] = raw
        manifest.append(dict(path=path, bytes=len(raw), sha256=sha(raw),
                             git_blob=git('rev-parse', COMMIT+':'+path).decode().strip(),
                             provenance_commit=COMMIT,
                             matches_historical_decoder_pin=pin is not None))
    controls = {}
    for name, digest in [('source_native_snapshot.rs', '37a00f8767af2a0002970e7a59d046861c4c8601f65c46fe0e86650694c6e318'),
                         ('native_snapshot_decode_tests.rs', '38e1bdc0fcf4a082a6af4e215a9d3ffac9cd6ad6fbbfd5d2c98b4e7226af591a')]:
        raw = (ROOT/DECODER/name).read_bytes()
        if sha(raw) != digest:
            raise ValueError('latest decoder source mismatch: '+name)
        controls[name] = raw
        manifest.append(dict(path='controls/'+name, bytes=len(raw), sha256=sha(raw),
                             provenance_path=DECODER+'/'+name, transformation=None))
    serial = (ROOT/SERIAL).read_bytes()
    if sha(serial) != '82fd059e3b813e6d1c9b65de03c8f15037d5d6d9ab15be8b51687160e2f98cb7':
        raise ValueError('serial full-history harness identity changed')
    original_path = ('#[path="/workspace/Research-Commons/'+PREFIX+'"]').encode()
    replacement = b'#[path="source_selected_prefix.rs"]'
    if serial.count(original_path) != 1:
        raise ValueError('expected one exact serial module path')
    controls['serial_early_late_history_tests.original.rs'] = serial
    controls['serial_early_late_history_tests.rs'] = serial.replace(original_path, replacement)
    controls['source_selected_prefix.rs'] = contents[PREFIX]
    for name in ['serial_early_late_history_tests.original.rs', 'serial_early_late_history_tests.rs',
                 'source_selected_prefix.rs']:
        raw = controls[name]
        manifest.append(dict(path='controls/'+name, bytes=len(raw), sha256=sha(raw),
                             provenance_path=PREFIX if name == 'source_selected_prefix.rs' else SERIAL,
                             transformation='one absolute module path relocated to sibling source; proof/test logic unchanged'
                             if name == 'serial_early_late_history_tests.rs' else None))
    total = sum(len(raw) for raw in contents.values())+sum(len(raw) for raw in controls.values())
    if total > 8*1024**2:
        raise ValueError('total restore cap')
    args.output.mkdir(parents=True, exist_ok=False)
    for path, raw in {**contents, **{'controls/'+k: v for k, v in controls.items()}}.items():
        target = args.output/path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
    report = dict(schema='recovered_public_parity_sources_v1', repository='Sodelin/Research-Commons',
                  commit=COMMIT, decoder_packet_sha256=PACKET_SHA,
                  historical_inrepo_rust_pins_matched=len(expected), files=manifest,
                  total_bytes=total, source_admission_certified=False,
                  native_refinement_proved=False, compiler_executed=False)
    encoded = (json.dumps(report, indent=2, sort_keys=True)+'\n').encode()
    args.manifest.write_bytes(encoded)
    (args.output/'RESTORED-SOURCES.json').write_bytes(encoded)
    print(json.dumps(dict(status='AUTHENTICATED_SOURCE_RECOVERY', files=len(manifest),
                          historical_pins=len(expected), bytes=total, manifest_sha256=sha(encoded))))


if __name__ == '__main__':
    main()
