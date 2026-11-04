#!/usr/bin/env python3
"""Prepare complete retained G7 game/rank bodies with a pinned hosted proof repair."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PINS={
 'G7ExactLawResourceGame':'86b878a239fc22e7ff6712593c4e849089a3d1c9986f04e64e3485ad12cff2be',
 'G7ExactLawRankCompression':'c2aa5ffb8617013c0a4fb11bc7aa20481a6e4c90a8c177856c442d80cf762bd2',
}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-store',type=Path,required=True)
    a=p.parse_args()
    parts=[];imports=[];rows=[];variants=[]
    for name,digest in PINS.items():
        raw=(a.source_store/(digest+'.lean')).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('ORIGINAL_SOURCE_CHANGED')
        if name=='G7ExactLawResourceGame':
            before=b'  simpa only [Homogeneous,not_forall,_root_.not_imp,exists_prop] using hn'
            after=b'  unfold Homogeneous at hn\n  push_neg at hn\n  exact hn'
            if raw.count(before)!=1:raise ValueError('EXACT_PROOF_VARIANT_REQUIRED')
            variant=(ROOT/'lean/hosted435/G7ExactLawResourceGame.lean').read_bytes()
            if variant!=raw.replace(before,after):raise ValueError('PROOF_VARIANT_DRIFT')
            variants.append({'module':name,'original_sha256':digest,
              'variant_sha256':hashlib.sha256(variant).hexdigest(),
              'only_change':'final losing_has_full_history_pair proof: explicit unfold/push_neg instead of removed _root_.not_imp simp name; statement and all executable definitions unchanged'})
            raw=variant
        body=[]
        for line in raw.decode().splitlines():
            if line.startswith('import '):
                module=line.split()[1]
                if module not in PINS and module not in imports:imports.append(module)
            else:body.append(line)
        parts.append('\n'.join(body)+'\n')
        rows.append({'module':name,'bytes':len(raw),'original_sha256':digest,
          'used_sha256':hashlib.sha256(raw).hexdigest(),
          'changes':'imports hoisted; complete remaining body retained, explicit proof variant separately pinned if present'})
    raw=('\n'.join('import '+n for n in imports)+'\n\n'+'\n'.join(parts)).encode()
    (ROOT/'lean/OnlineG7ExactLawGame.lean').write_bytes(raw)
    (ROOT/'lean/G7ExactLawGame-SOURCE-MAP.json').write_text(json.dumps({
      'kind':'complete_retained_game_and_rank_bodies_with_explicit_hosted_proof_variant',
      'original_sources':rows,'hosted_proof_variants':variants,'external_imports':imports,'virtual_bytes':len(raw),
      'virtual_sha256':hashlib.sha256(raw).hexdigest(),'full_actual_source_instantiation':False,
      'effective_QE_or_policy_extraction':False,'native_import_or_object_acceptance':False,
      'compiler_invoked_by_preparation':False},indent=2)+'\n')
    print(json.dumps({'source_only_bytes':len(raw),'virtual_sha256':hashlib.sha256(raw).hexdigest(),
      'complete_retained_bodies':len(rows),'compiler_invoked':False}))

if __name__=='__main__':main()
