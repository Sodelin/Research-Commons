#!/usr/bin/env python3
"""Execute the source-certified n4/r1 two-configuration pooled policy."""
from pathlib import Path
import argparse
import json
import sys
import sympy as sp
ROOT = Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'sourcekit'))
from solver import prepare_request, InvalidInput, Unsupported, verify_witness, target_json, graph_json, physical_realization, digest
from check_forced_pair_policy import witness


def execute(request):
    n, ids, modes, taxa, rows = prepare_request(request)
    if n != 4 or len(ids) != 1 or len(rows) != 1 or rows[0]['kind'] != 'unrooted_splits':
        raise Unsupported('This policy needs complete n4/r1, one pooled unrooted quartet readout.')
    row=rows[0]
    if set(row['samples'])!={f'L{i}' for i in range(4)} or any(len(v)!=1 for v in row['samples'].values()):
        raise Unsupported('One original sampled copy per original taxon required.')
    weights={0:sp.S.Zero,1:sp.S.Zero}
    for weight,forcing in row['program']:
        if set(forcing)!={'H0'} or forcing['H0'] not in (0,1):
            raise Unsupported('The programme must pool ONLY the two full original forcing rows.')
        weights[forcing['H0']]+=weight
    if not all(0<weights[bit]<1 for bit in (0,1)):
        raise Unsupported('Both original forcing configurations need strictly positive weights.')
    certificate=json.loads((ROOT/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes())
    copy_to_leaf={copies[0]:leaf for leaf,copies in row['samples'].items()}
    observed={}
    for event,p in row['observed'].items():
        if len(event)!=1:
            raise InvalidInput('A fully resolved quartet law has one cut per outcome.')
        cut=tuple(sorted(tuple(sorted(copy_to_leaf[label] for label in side)) for side in event[0]))
        observed[(cut,)]=p
    coordinates=[tuple(tuple(tuple(side) for side in cut) for cut in event)
                 for event in certificate['coordinate_order']]
    probabilities=[observed.get(event,sp.S.Zero) for event in coordinates]
    base=min(probabilities);selected=tuple(i for i,p in enumerate(probabilities) if p>base)
    def no_source(reason):
        return {'status':'NO_SOURCE_FOR_FIXED_MENU_BY_COMPLETE_IMAGE_CERTIFICATE',
                'request_sha256':digest(request),'reason':reason,
                'scope':'complete546-source n4/r1 original registry and ONLY the two full forcing rows; no unknown-size or empirical NO',
                'Lean_verification_claimed':False}
    if base<=0 or not selected or len(selected)>2:
        return no_source('Strict positive source images have a positive baseline and one or two coordinates strictly above it.')
    representatives={tuple(v['target_coordinate'] for v in r['forced_rows']):r
                     for r in certificate['surjection_representatives']}
    pairs=[(selected[0],selected[0])] if len(selected)==1 else [selected,tuple(reversed(selected))]
    for a,b in pairs:
        if a==b:
            s=t=3*base
        else:
            s=1-(probabilities[a]-base)/weights[0]
            t=1-(probabilities[b]-base)/weights[1]
        if not (0<s<1 and 0<t<1):
            continue
        source,values=witness(representatives[(a,b)],s,t)
        verify_witness(source,modes[0],rows,values)
        actual=target_json(source)['nontrivial_displayed_split_union']
        expected=sorted(event[0] for i,event in enumerate(coordinates) if i in selected)
        if actual!=expected:
            raise InvalidInput('Constructed actual target differs from the source-certified min rule.')
        return {'status':'IDENTIFIED_ACTUAL_Q_BY_TWO_CONFIGURATION_ONE_CALL_POLICY',
                'request_sha256':digest(request),'inheritance_mechanism':modes[0],
                'engine_taxon_mapping':{f'L{i}':taxon for i,taxon in enumerate(taxa)},
                'original_hybrid_mapping':{'H0':ids[0]},'strict_positive_programme_weights':[str(weights[i]) for i in (0,1)],
                'identified_engine_split_union':actual,
                'identified_original_taxon_split_union':[[[taxa[int(label[1:])] for label in side] for side in cut] for cut in actual],
                'actual_source':graph_json(source),'source_values':values,
                'physical_realization':physical_realization(source,values),
                'verification':'ACTUAL_SHARED_SOURCE_WITNESS_RECOMPILED_AND_COMPLETE546_SOURCE_IMAGE_POLICY_CERTIFICATE',
                'trajectory_cost':{'exact_calls':1,'configurations':2,'original_controlled_sites':1},
                'scope':'The complete n4/r1 source class, one-copy unlabelled pooled unrooted law, free positive edge clocks, menu ONLY original forcing0/1.',
                'empirical_admission_or_unknown_size_termination_claimed':False,
                'generic_CAD_policy_extraction_claimed':False,'Lean_verification_claimed':False}
    return no_source('Both ordered target-pair images violate their strict quantitative survival bounds for the supplied known weights.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('request');p.add_argument('--output',required=True);a=p.parse_args()
    try:result=execute(json.loads(Path(a.request).read_bytes()))
    except (InvalidInput,Unsupported,KeyError,TypeError,ValueError) as error:
        print(json.dumps({'status':'POLICY_INPUT_UNSUPPORTED_OR_INVALID','reason':str(error)}))
        return 2
    Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','trajectory_cost','reason') if k in result},indent=2));return 0


if __name__=='__main__':raise SystemExit(main())
