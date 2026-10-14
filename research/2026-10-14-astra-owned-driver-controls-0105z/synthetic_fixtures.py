"""Synthetic metadata and byte fixtures only: no Lean objects or processes."""
import hashlib
import json
from pathlib import Path


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def exact(path):
    raw = path.read_bytes()
    return dict(bytes=len(raw), sha256=sha(raw))


def external_fixture(root):
    """One shared synthetic metadata set. No selected source/object exists."""
    support, external = root / 'support', root / 'external'
    support.mkdir(); external.mkdir()
    modules = []
    for index in range(3591):
        selected = dict(module=f'Synthetic.External{index}', source=f'SYNTHETIC_SOURCE_{index}',
            source_sha256=sha(b'SYNTHETIC_UNCOMPILED_BYTES'), repo='SYNTHETIC_REPO',
            target=f'SYNTHETIC_OBJECT_ABSENT_{index}', imports=[])
        modules.append(selected)
        write(external / f'{index:04d}.json', dict(selected, exit_code=0, synthetic_only=True))
        for suffix in ['stdout', 'stderr']:
            (external / f'{index:04d}.{suffix}').write_bytes(b'')
    write(support / 'EXTERNAL-PLAN.json', dict(modules=modules, synthetic_only=True))
    (external / 'PLAN.json').write_bytes((support / 'EXTERNAL-PLAN.json').read_bytes())
    write(root / 'SYNTHETIC-ONLY.json', dict(production_source_objects=False,
        actual_external_authentication=False, synthetic_receipt_count=3591,
        note='These invented metadata rows cannot satisfy the real guarded builder.'))
    return support, external


class Owned:
    def __init__(self, root, driver, provider_count=4):
        self.root, self.driver = root, driver
        self.state = root / 'owned-state'
        self.output = root / 'guard-output'
        self.directory = root / 'production'
        self.output.mkdir(); self.directory.mkdir(); self.state.mkdir()
        self.namespace = {'synthetic_only': True, 'routing': 'NO_ACTUAL_OBJECTS'}
        self.namespace_sha = sha(json.dumps(self.namespace, sort_keys=True).encode())
        self.modules = []
        self.sources = {}
        for index in range(provider_count + 1):
            name = f'Synthetic.Provider{index}' if index < provider_count else 'Synthetic.Adapter'
            raw = ('SYNTHETIC UNCOMPILED SOURCE FOR ' + name + '\n').encode()
            self.sources[index] = raw
            self.modules.append(dict(module=name, sha256=sha(raw),
                kind='accepted1613' if index < provider_count else 'new_adapter', synthetic_only=True))
        self.plan = dict(modules=self.modules, namespace_sha256=self.namespace_sha,
                         runner_sha256=driver.BUILDER_SHA, synthetic_only=True)
        write(self.state / 'PLAN.json', self.plan)
        write(self.state / 'NAMESPACE-RESOLUTION.json', self.namespace)
        self.profile = dict(expected_start_index=1, fresh_budget=1, batch_id=2,
            batch_output=str(self.output), cwd=str(root), guard_sha256=driver.GUARD_SHA,
            child_command=['SYNTHETIC_BUILDER_NEVER_EXECUTED'], limits={'synthetic_only': True})
        write(root / 'SYNTHETIC-ONLY.json', dict(actual_guard=False, actual_compiler=False,
            production_provider_authenticated=False, process_identity_observation='injected test observation'))

    def source_path(self, index):
        return self.state / 'source' / Path(*self.modules[index]['module'].split('.')).with_suffix('.lean')

    def row(self, index, mode='FRESH_SOURCE_COMPILE', code=0):
        selected = self.modules[index]
        row = dict(module=selected['module'], source_sha256=selected['sha256'], kind=selected['kind'],
            exit_code=code, execution=mode, runner_sha256=self.driver.BUILDER_SHA,
            namespace_sha256=self.namespace_sha, artifacts={}, synthetic_only=True)
        self.source_path(index).parent.mkdir(parents=True, exist_ok=True)
        self.source_path(index).write_bytes(self.sources[index])
        if mode == 'FRESH_SOURCE_COMPILE':
            for suffix in ['stdout', 'stderr']:
                raw = ('synthetic ' + suffix + '\n').encode()
                (self.state / f'{index:04d}.{suffix}').write_bytes(raw)
                row[suffix + '_sha256'] = sha(raw)
        else:
            row['origin'] = dict(kind='SYNTHETIC_REUSE_NO_OBJECT_AUTHENTICATION', receipt={'synthetic_only': True})
        write(self.state / f'{index:04d}.json', row)
        return row

    def checkpoint(self, capture, helper):
        self.row(0)
        previous_state = self.driver.STATE
        self.driver.STATE = self.state
        try:
            self.before = self.driver.before_state(capture, helper, dict(synthetic_only=True))
        finally:
            self.driver.STATE = previous_state
        write(self.directory / 'PRE-BATCH-STATE.json', self.before)
        write(self.directory / 'INTENT.json', dict(prebatch_sha256=sha((self.directory / 'PRE-BATCH-STATE.json').read_bytes())))
        write(self.directory / 'LAUNCH.json', dict(synthetic_only=True, launch_is_completion=False))

    def terminal(self, fresh, clones, *, exit_code=0, stop=None, error=None, reuse_summary=None):
        events = [dict(index=index, module=self.modules[index]['module'], exit_code=code)
                  for index, code in fresh]
        if exit_code == 0 and stop is None:
            events.append(dict(status='BATCH_COMPLETE', freshly_compiled=len(fresh),
                authenticated_reuse=(1 + len(clones) if reuse_summary is None else reuse_summary),
                complete=False, synthetic_only=True))
        raw = b''.join((json.dumps(row) + '\n').encode() for row in events)
        (self.output / 'stdout').write_bytes(raw); (self.output / 'stderr').write_bytes(b'')
        receipt = dict(command=self.profile['child_command'], cwd=self.profile['cwd'],
            limits=self.profile['limits'], runner_sha256=self.profile['guard_sha256'],
            exit_code=exit_code, stop=stop, outputs={name:exact(self.output / name) for name in ['stdout','stderr']},
            synthetic_only=True)
        if error is not None:
            receipt['error'] = error
        write(self.output / 'RECEIPT.json', receipt)
        for name in ['guard.stdout', 'guard.stderr']:
            (self.directory / name).write_bytes(b'SYNTHETIC GUARD LOG; NO PROCESS\n')

    def successful(self, capture, helper):
        self.checkpoint(capture, helper)
        self.row(1, 'AUTHENTICATED_REUSE'); self.row(2)
        self.terminal([(2, 0)], [1])

    def previous_finish(self, capture, helper):
        """A synthetic earlier closed checkpoint for preliminary resume tests."""
        self.row(0)
        prior = self.root / 'evidence/production-001'; prior.mkdir(parents=True)
        delta = helper.preserve_delta(self.state, prior, {}, {})
        write(prior / 'FINISH.json', dict(provider_batch_verified=True, owned_state=str(self.state),
            next_owned_receipt_index=1, provider_preparation_complete=False,
            owned_delta_sha256=delta, synthetic_only=True))
        return prior
