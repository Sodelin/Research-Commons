"""Read-only identity/closure review; does not compile or certify draft mathematics."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess

REPO = pathlib.Path('/workspace/Research-Commons')
PACKET = REPO / 'research/2026-10-11-dot-g4-actual-span-source-interface-0011z'
OWN = REPO / 'research/2026-10-10-codex-lean-rust-parity'
BASE = pathlib.Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z')
COMMIT = '823df1803bee087aec9faf6e9db4f0c69b5f03e0'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def git_bytes(spec):
    return subprocess.check_output(['git', 'show', spec], cwd=REPO)


def imports(data):
    return re.findall(r'^\s*import\s+(\S+)\s*$', data.decode(), re.M)


def main():
    acceptance = OWN / 'lean/HISTORY-SURVIVAL-UNION-1504-ACCEPTANCE.json'
    assert digest(acceptance.read_bytes()) == '554461bf84edc6eba14ecb2a7feba86c8632a53f0bfedc81b15b88222019c838'
    graph_path = BASE / 'DEPENDENCY-GRAPH.json'
    assert digest(graph_path.read_bytes()) == 'e05a87db2b34f42aada87a958f7ff9114c68a817458b5919f7ecac62386fbacd'
    accepted = load(graph_path)['targets']['current/connected']['modules']
    assert len(accepted) == 1504
    files = []
    for line in (PACKET / 'MANIFEST.sha256').read_text().splitlines():
        if not line:
            continue
        expected, name = line.split('  ', 1)
        path = PACKET / name
        data = path.read_bytes()
        assert digest(data) == expected
        assert git_bytes(COMMIT + ':' + str(path.relative_to(REPO))) == data
        files.append({'path': str(path), 'bytes': len(data), 'sha256': expected})
    assert len(files) == 9
    pins = load(PACKET / 'DRAFT-DEPENDENCY-PINS.json')
    locators = load(PACKET / 'PUBLIC-SOURCE-LOCATORS.json')
    assert pins['base_graph_sha256'] == locators['base_graph_sha256']
    assert locators['source_commit'] == '38f51fdff9ffa427ec7dabb591ef94711c322a7a'
    base = pins['base_modules']
    mapped = pins['existing_source_transport_consumers_not_new_imports']
    drafts = pins['modules']
    assert len(base) == pins['base_closure_module_count'] == 217
    assert len(mapped) == 4 and not set(base) & set(mapped)
    assert len(drafts) == 2
    assert set(locators['sources']) == set(base) | set(mapped)
    sources = []
    for module, row in {**base, **mapped}.items():
        assert row == accepted[module]
        locator = locators['sources'][module]
        assert locator['sha256'] == row['sha256']
        path = BASE / 'source-store' / (row['sha256'] + '.lean')
        data = path.read_bytes()
        assert digest(data) == row['sha256']
        assert imports(data) == row['imports']
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert blob == locator['git_blob']
        assert git_bytes(blob) == data
        assert locator['immutable_blob_url'] == 'https://api.github.com/repos/Sodelin/Research-Commons/git/blobs/' + blob
        sources.append({'module': module, 'sha256': row['sha256'], 'git_blob': blob, 'bytes': len(data)})
    for module, row in drafts.items():
        data = (PACKET / (module + '.lean')).read_bytes()
        assert digest(data) == row['sha256'] and imports(data) == row['imports']
    closure = set()

    def visit(module):
        if module in drafts:
            for child in drafts[module]['imports']:
                visit(child)
        elif module in accepted:
            if module in closure:
                return
            closure.add(module)
            for child in accepted[module]['imports']:
                visit(child)
        else:
            assert module.startswith('Mathlib.') or module in {'Mathlib', 'Lean', 'Std'}

    for module in drafts:
        visit(module)
    assert closure == set(base)
    result = {
        'status': 'PASS_PACKET_AND_INHERITED_SOURCE_IDENTITIES_STATIC_ONLY',
        'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'packet_commit': COMMIT, 'files': files, 'inherited_sources': sources,
        'base_closure_modules': 217, 'separate_existing_consumers': 4,
        'drafts': drafts,
        'accepted_base_graph_sha256': digest(graph_path.read_bytes()),
        'peer_prepared_graph_sha256_reported_only': pins['base_graph_sha256'],
        'peer_prepared_graph_authenticated': False,
        'compilation_performed': False, 'draft_kernel_acceptance': False,
        'accepted1504_changed': False, 'new_obligation_ids': 0,
        'scope': 'Exact packet bytes, inherited source bodies, literal imports and recursive closure. New draft mathematics remains uncompiled; await terminal peer union receipt before the separate additive compilation requested by DOT.',
    }
    out = OWN / 'quality/NEWEST-DOT-G4-ACTUAL-SPAN-SOURCE-REVIEW-20261011T0040Z.json'
    assert not out.exists()
    out.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'path': str(out), 'sha256': digest(out.read_bytes()), 'status': result['status'], 'sources': len(sources)}))


if __name__ == '__main__':
    main()
