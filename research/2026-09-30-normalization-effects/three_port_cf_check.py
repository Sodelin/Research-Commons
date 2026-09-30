"""Exact common-inheritance obstruction to a fixed three-port tree star.

All original population edges have length log(2). Two sampled taxa are in
each of clades A and C; one is below the hybrid. Both parent switchings have
identical unrooted topology, but their metric mixture is not one metric tree.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import normalization_effects_check as helper


def main():
    fixed=[('R','SC'),('R','U'),('U','V'),('V','SA'),
           ('SA','A'),('SA','B'),('SC','C'),('SC','D'),('H','E')]
    observations=[]
    for parent in ['U','V']:
        edges=[(a,b,F(1,2)) for a,b in fixed+[(parent,'H')]]
        observations.append(helper.weighted_quartets(edges))
    assert observations[0][1]==observations[1][1]
    assert all(observations[0][0][q][0]==observations[1][0][q][0] for q in observations[0][0])
    survivals={q:sum((obs[0][q][1] for obs in observations),F(0))/2 for q in observations[0][0]}
    phi_A=survivals[tuple('ABCE')]
    phi_C=survivals[tuple('ACDE')]
    phi_AC=survivals[tuple('ABCD')]
    assert (phi_A,phi_C,phi_AC)==(F(3,8),F(3,16),F(1,16))
    assert phi_A*phi_C==F(9,128) and phi_AC!=phi_A*phi_C
    receipt={'status':'PASS','model':'exact analytical NMSCcom tree mixture',
       'source_graph_fixed_edges':fixed,'hybrid_parents':['U','V'],
       'all_original_edge_survivals':'1/2','inheritance':'1/2',
       'both_switchings_same_unrooted_split_set':True,
       'phi_A':str(phi_A),'phi_C':str(phi_C),'phi_AC':str(phi_AC),
       'fixed_star_required_product':str(phi_A*phi_C),
       'observed_correct_CF_2A_2C':str(1-F(2,3)*phi_AC),
       'fixed_star_predicted_correct_CF_2A_2C':str(1-F(2,3)*phi_A*phi_C),
       'one_fixed_three_port_star_preserves_all_quartet_CFs':False,
       'source_admission':'R splits C-clade from U-side, so R is LSA; U,V,H form a triangle with pendant hybrid child; all taxon grafts can be exterior. Manual admission; switch-tree exact checks executed.',
       'scope':'Cannot replace this three-port blob by one fixed metric tree star while preserving all quartet CFs. Does not rule out other smaller reticulate models.',
       'not_claimed':['NMSCind calculation','full joint law comparison','biological experiment','Lean']}
    Path(__file__).with_name('three-port-cf-checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))


if __name__=='__main__':main()
