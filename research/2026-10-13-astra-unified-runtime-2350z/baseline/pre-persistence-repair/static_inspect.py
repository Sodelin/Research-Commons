#!/usr/bin/env python3
"""Read/hash/AST-inspect only; never imports or executes the runtime."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def constant(node):
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        return constant(node.left) * constant(node.right)
    return ast.literal_eval(node)


def main():
    raw = (HERE / 'runtime.py').read_bytes()
    tree = ast.parse(raw, filename='runtime.py')
    names = {'PINS', 'CHECKERS', 'SOURCES', 'MAX_BYTES', 'MAX_BINARY_BYTES'}
    constants = {node.targets[0].id: constant(node.value) for node in tree.body
        if isinstance(node, ast.Assign) and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name) and node.targets[0].id in names}
    providers = []
    for relative, pin in constants['PINS'].items():
        body = (ROOT / relative).read_bytes()
        actual = hashlib.sha256(body).hexdigest()
        assert actual == pin, relative
        providers.append(dict(path=relative, bytes=len(body), sha256=actual))
    runtime = dict(path='runtime.py', bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
    now = datetime.now(timezone.utc).isoformat()
    ledger = dict(schema='astra_unified_runtime_source_pins_v1', status='SOURCE_ONLY_DRAFT',
        source_authenticated_utc=now, execution_performed=False,
        fresh_native_build=False, fresh_Lean_build=False, primary_runtime=runtime,
        exact_selected_providers=providers, approved_checker_profiles=constants['CHECKERS'],
        exact_delegate_modules=constants['SOURCES'], byte_transport_limit=constants['MAX_BYTES'],
        checker_file_byte_limit=constants['MAX_BINARY_BYTES'],
        selected_readout_scope='Original selected native formal readouts; physical/source UNKNOWN even when all rows match.',
        source_search_scope='Unchanged exact witness or exclusion within the declared verified covered class; no global-size or arbitrary-input closure.',
        support_emission_scope='Existing conditional literal certificate-to-support sources, deduplicated by exact original certificate identity; uncompiled by this runtime.',
        artifact_reuse='Pinned existing source delegation and historical closed build/observation records; no new execution or universal native correctness proof.',
        rc1_authentication='Delegated unchanged to pinned native_bridge.authenticate; no replacement parser, arithmetic or source-to-native refinement.',
        runtime_unverified=True, publication_verified=False)
    receipt = dict(schema='astra_runtime_static_inspection_v1', status='STATIC_SOURCE_PASS_ONLY',
        observed_utc=now,
        method='ast.parse plus literal AST constants and byte hashing only; runtime module not imported or executed',
        runtime=runtime, helper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        provider_files=len(providers), all_exact_hashes_matched=True,
        initial_helper_failure=dict(stage='ad hoc AST constant extraction, before output writes',
            error='ValueError: malformed node or string on line 15: ast.BinOp',
            repair='This helper evaluates only literal multiplication in MAX_BINARY_BYTES; no eval, runtime import or source change.'),
        runtime_controls_run=0, native_invocations=0, compiler_invocations=0,
        explicitly_unverified=['Runtime behavior and error paths', 'Composition control fixtures',
            'Resource-guard execution', 'Emitted Lean compilation', 'Remote publication'],
        review_kind='Agent static source inspection, not independent human mathematical review')
    for name, value in [('SOURCE-PINS.json', ledger), ('STATIC-INSPECTION.json', receipt)]:
        with (HERE / name).open('x') as stream:
            json.dump(value, stream, indent=2, sort_keys=True)
            stream.write('\n')
    print(json.dumps(dict(provider_files=len(providers), runtime_sha256=runtime['sha256'],
                          ast_parse='PASS', runtime_execution=False)))


if __name__ == '__main__':
    main()
