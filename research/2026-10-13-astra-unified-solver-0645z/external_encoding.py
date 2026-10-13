"""Fixed external legal mixed-comb observation encoding.

Every copy label, allocation, joint PMF, mask table, passive pruning event and
normalization is determined before a candidate source. This is the executable
description of the selected padded-comb interface; source-law extraction and
its Lean parser correspondence are separate obligations.
"""
from fractions import Fraction
from math import factorial

from certificates import common_packet, digest, rational


def fixed_queries(menu):
    common_packet(menu)
    queries=[]
    for pair in menu['pairs']:
        cert=pair['certificate']
        for k, moment in enumerate(cert['moments'],start=1):
            # Tags deliberately separate baseline taxon labels from the copies
            # kept by the observable event. No ID is a candidate graph index.
            b='selected:B'
            aa=[f'selected:A{i}' for i in range(1,k+1)]
            allocation={b:pair['j'],**{copy:pair['i'] for copy in aa},
                        **{'baseline:'+taxon:taxon for taxon in menu['taxa']}}
            comb=b
            # The first cherry is (B,A1), then A2,...,Ak. Orientation is erased
            # by the unranked output semantics, not a change to comb history.
            for copy in aa:
                comb=[comb,copy]
            coefficient=Fraction(2**k,factorial(k+1)*factorial(k))
            row=dict(schema='external_padded_mixed_comb_row_v1',
                     directed_pair=[pair['i'],pair['j']],level=k,
                     allocation=allocation,configuration_table=menu['configurations'],
                     protected_hybrid_ids=menu['protected_hybrids'],
                     unprotected_control=None,
                     mask_semantics=dict(null='natural original stored bank',
                                         bit0='false: original incoming-parent bit 0',
                                         bit1='true: original incoming-parent bit 1'),
                     readout=dict(kind='passive_pruned_unranked_forest_event',
                                  keep=[b]+aa,forest=[comb],child_orientation='erased'),
                     normalized_moment=str(rational(moment)),
                     comb_coefficient=str(coefficient),
                     required_event_probability=str(coefficient*rational(moment)),
                     probability_role='derived requirement from supplied normalized moment; no source row checked',
                     certificate_sha256=digest(cert))
            row['row_sha256']=digest(row)
            queries.append(row)
    return dict(schema='fixed_external_common_query_menu_v1',
                source_input_sha256=digest(menu),taxa=menu['taxa'],
                protected_edges=menu['protected_edges'],protected_hybrids=menu['protected_hybrids'],
                parameter_constraints=menu['parameter_constraints'],queries=queries,
                formal_provider=dict(module='G4WholeProfileDetermination',
                  sha256='fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09',
                  declarations=['randomizedLegalCombMoment','actual_randomized_legal_moment']),
                actual_source_binding_checked=False,parser_Lean_refinement_proved=False)
