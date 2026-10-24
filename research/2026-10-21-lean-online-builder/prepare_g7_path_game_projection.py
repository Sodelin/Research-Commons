#!/usr/bin/env python3
"""Compose only authored source with the exact checked game/budget projection."""
import hashlib
import json
from pathlib import Path
from prepare_chart_form_projection import no_imports

ROOT=Path(__file__).resolve().parent

def main():
    previous=(ROOT/'lean/OnlineG7FinitePathBudgetBridge.lean').read_bytes()
    if hashlib.sha256(previous).hexdigest()!='1b52d64139d9fc7d33558e36c96fd355dcb1ed434ae76a8cc16b7d77d7db1a6d':
        raise ValueError('CHECKED_GAME_BUDGET_COMPONENT_CHANGED')
    proof=(ROOT/'lean/G7FinitePathGame.lean').read_bytes()
    raw=previous+b'\n'+no_imports(proof.decode()).encode()
    (ROOT/'lean/OnlineG7FinitePathGame.lean').write_bytes(raw)
    (ROOT/'lean/G7FinitePathGame-SOURCE-MAP.json').write_text(json.dumps({
        'kind':'retained_checked_game_budget_plus_semantic_horizon_composition',
        'previous_checked_game_budget_sha256':hashlib.sha256(previous).hexdigest(),
        'authored_source_sha256':hashlib.sha256(proof).hexdigest(),
        'virtual_bytes':len(raw),'virtual_sha256':hashlib.sha256(raw).hexdigest(),
        'existing_game_definitions_changed':False,'Rust_AST_or_resource_refinement':False,
        'actual_source_or_free_prefix_admission':False,'compiler_invoked_by_preparation':False},
        indent=2)+'\n')
    print(json.dumps({'source_only_bytes':len(raw),'virtual_sha256':hashlib.sha256(raw).hexdigest(),
                      'compiler_invoked':False}))

if __name__=='__main__':main()
