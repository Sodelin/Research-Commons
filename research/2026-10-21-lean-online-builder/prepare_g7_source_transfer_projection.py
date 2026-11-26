#!/usr/bin/env python3
"""Append source-only transfer proofs to the retained checked game component."""
import hashlib
import json
from pathlib import Path
from prepare_chart_form_projection import no_imports

ROOT=Path(__file__).resolve().parent

def main():
    previous=(ROOT/'lean/OnlineG7ExactLawGame.lean').read_bytes()
    if hashlib.sha256(previous).hexdigest()!='b400cec0eb1e982e3ca8865cb6bd22b9b8a03b9fd4eb22f5cb139913476265a6':
        raise ValueError('CHECKED_GAME_COMPONENT_CHANGED')
    proof=(ROOT/'lean/G7ExactLawSourceTransfer.lean').read_bytes()
    raw=previous+b'\n'+no_imports(proof.decode()).encode()
    (ROOT/'lean/OnlineG7ExactLawSourceTransfer.lean').write_bytes(raw)
    (ROOT/'lean/G7ExactLawSourceTransfer-SOURCE-MAP.json').write_text(json.dumps({
        'kind':'retained_checked_game_plus_conditional_source_representation_transfer',
        'previous_checked_game_sha256':hashlib.sha256(previous).hexdigest(),
        'authored_source_sha256':hashlib.sha256(proof).hexdigest(),
        'virtual_bytes':len(raw),'virtual_sha256':hashlib.sha256(raw).hexdigest(),
        'existing_game_definitions_changed':False,'native_source_representation_constructed':False,
        'effective_source_or_policy_selection':False,'compiler_invoked_by_preparation':False},
        indent=2)+'\n')
    print(json.dumps({'source_only_bytes':len(raw),'virtual_sha256':hashlib.sha256(raw).hexdigest(),
                      'compiler_invoked':False}))

if __name__=='__main__':main()
