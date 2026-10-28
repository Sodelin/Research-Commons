#!/usr/bin/env python3
"""Reuse the exact checked full game/rank/transfer virtual source, then extend it.

Preparation is source-only. It invokes no Lean, runtime, process or writer
controller. The output is authored source, not an execution record.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = '2804232d7daea06e5c41e596ebb497c05c94d3b1ec9dbd7e8286f5fad24a90c4'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    prefix = (ROOT/'lean/OnlineG7ExactLawSourceTransfer.lean').read_bytes()
    if sha(prefix) != BASE:
        raise ValueError('CHECKED_FULL_GAME_TRANSFER_PREFIX_CHANGED')
    if any(line.startswith('import ') and not line.startswith(('import Mathlib.', 'import Lean.'))
           for line in prefix.decode().splitlines()):
        raise ValueError('UNRESOLVED_PREFIX_IMPORT')
    source = (ROOT/'lean/G7FiniteTargetReceiver.lean').read_bytes()
    body = '\n'.join(line for line in source.decode().splitlines()
                     if not line.startswith('import ')) + '\n'
    virtual = b'import Mathlib.Data.Real.Basic\n' + prefix + b'\n' + body.encode()
    if len(virtual) > 262144:
        raise ValueError('EXISTING_HOSTED_SOURCE_BOUND')
    (ROOT/'lean/OnlineG7FiniteTargetReceiver.lean').write_bytes(virtual)
    report = {'kind': 'exact_checked_full_game_rank_transfer_plus_finite_target_receiver',
        'prefix': 'lean/OnlineG7ExactLawSourceTransfer.lean',
        'prefix_bytes': len(prefix), 'prefix_sha256': BASE,
        'prefix_retained_byte_identically': True,
        'source': 'lean/G7FiniteTargetReceiver.lean',
        'source_bytes': len(source), 'source_sha256': sha(source),
        'virtual': 'lean/OnlineG7FiniteTargetReceiver.lean',
        'virtual_bytes': len(virtual), 'virtual_sha256': sha(virtual),
        'additional_external_import': 'Mathlib.Data.Real.Basic',
        'authored_source_change': 'Only its two imports are removed in the virtual extension.',
        'native_ast_or_source_representation_constructed': False,
        'effective_selector_or_backend_run': False,
        'compiler_invoked_by_preparation': False}
    (ROOT/'lean/G7FiniteTargetReceiver-SOURCE-MAP.json').write_text(
        json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
