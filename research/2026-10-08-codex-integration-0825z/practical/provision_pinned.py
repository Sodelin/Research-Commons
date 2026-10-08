"""Recover public pinned Rust/build inputs into isolated scratch; this uses network.

Subsequent Cargo commands use --locked --offline and a checksum-verified vendor
tree. No toolchain, compiled binary, cache, or dependency source is published.
"""
from pathlib import Path
import concurrent.futures
import hashlib
import json
import subprocess
import tarfile
import time
import tomllib
import urllib.request

BASE = Path('/workspace/scratch/integration-practical')
PACKET = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def fetch(url, expected=None):
    data = urllib.request.urlopen(url, timeout=60).read()
    if expected and sha(data) != expected:
        raise RuntimeError('download checksum mismatch: ' + url)
    return data


def main():
    started = time.time()
    downloads = BASE / 'downloads'
    downloads.mkdir(exist_ok=False)
    url = 'https://static.rust-lang.org/dist/channel-rust-1.90.0.toml'
    manifest = fetch(url)
    manifest_sha = fetch(url + '.sha256').decode().split()[0]
    if sha(manifest) != manifest_sha:
        raise RuntimeError('toolchain channel manifest checksum mismatch')
    (downloads / 'channel-rust-1.90.0.toml').write_bytes(manifest)
    config = tomllib.loads(manifest.decode())
    triple = 'x86_64-unknown-linux-gnu'
    components = []
    for name in ('rustc', 'cargo', 'rust-std'):
        target = config['pkg'][name]['target'][triple]
        components.append((name, target['xz_url'], target['xz_hash']))

    def component(item):
        name, address, digest = item
        data = fetch(address, digest)
        archive = downloads / Path(address).name
        archive.write_bytes(data)
        extract = BASE / ('dist-' + name)
        extract.mkdir(exist_ok=False)
        with tarfile.open(archive) as tar:
            tar.extractall(extract, filter='data')
        installer = next(extract.glob('*/install.sh'))
        result = subprocess.run(['bash', str(installer), '--prefix=' + str(BASE / 'toolchain'),
                                 '--disable-ldconfig'], capture_output=True, check=False)
        (PACKET / 'logs' / ('provision-' + name + '.stdout')).write_bytes(result.stdout)
        (PACKET / 'logs' / ('provision-' + name + '.stderr')).write_bytes(result.stderr)
        if result.returncode:
            raise RuntimeError('toolchain installer failed: ' + name)
        return {'component': name, 'url': address, 'sha256': digest, 'bytes': len(data),
                'installer_exit': result.returncode}

    # Installation writes one prefix, so keep it sequential.
    toolchain = [component(item) for item in components]
    lock_path = PACKET / 'recovered/research/2026-10-08-cloud-rust-signed-probe-0122z/Cargo.lock'
    lock = tomllib.loads(lock_path.read_text())
    vendor = BASE / 'vendor'
    vendor.mkdir(exist_ok=False)

    def crate(package):
        name, version, digest = package['name'], package['version'], package['checksum']
        address = f'https://static.crates.io/crates/{name}/{name}-{version}.crate'
        data = fetch(address, digest)
        archive = downloads / f'{name}-{version}.crate'
        archive.write_bytes(data)
        with tarfile.open(archive) as tar:
            tar.extractall(vendor, filter='data')
        directory = vendor / f'{name}-{version}'
        files = {str(path.relative_to(directory)): sha(path.read_bytes())
                 for path in directory.rglob('*') if path.is_file()}
        (directory / '.cargo-checksum.json').write_text(json.dumps({'files': files, 'package': digest}))
        return {'name': name, 'version': version, 'url': address, 'lock_checksum': digest,
                'archive_sha256': sha(data), 'archive_bytes': len(data), 'source_files': len(files)}

    packages = [p for p in lock['package'] if 'source' in p]
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
        crates = list(pool.map(crate, packages))
    cargo_home = BASE / 'cargo-home'
    cargo_home.mkdir(exist_ok=False)
    (cargo_home / 'config.toml').write_text('[source.crates-io]\nreplace-with = "vendored-sources"\n'
                                          '[source.vendored-sources]\ndirectory = "' + str(vendor) + '"\n')
    versions = {name: subprocess.check_output([str(BASE / 'toolchain/bin' / name), '--version', '--verbose'], text=True)
                for name in ('rustc', 'cargo')}
    if '1159e78c4747b02ef996e55082b704c09b970588' not in versions['rustc']:
        raise RuntimeError('unexpected rustc commit')
    result = {'schema': 'integration_practical_network_provisioning_v1', 'network_used': True,
              'subsequent_build_offline_is_not_provisioning_offline': True,
              'channel_url': url, 'channel_sha256': manifest_sha, 'toolchain': toolchain,
              'lock_sha256': sha(lock_path.read_bytes()), 'crates': crates, 'versions': versions,
              'started_unix': started, 'ended_unix': time.time()}
    (PACKET / 'logs/PROVISIONING.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'PINNED_INPUTS_RECOVERED', 'crates': len(crates), 'network_used': True}))


if __name__ == '__main__':
    main()
