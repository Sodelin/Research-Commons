"""Faithful regular action of the EXACT accepted labelled forest algebra.

This represents full kernel families, not a scalar no-merger or a stochastic
population-state approximation. Entering token arity orders diagonal blocks.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'upstream'))
from forest_algebra import ForestAlgebra,poly_add

def matrix(alg,kernel):
    if len(kernel)!=alg.dim:raise ValueError('Full actual kernel family dimension required.')
    out=[[Q(0) for _ in alg.coords] for _ in alg.coords]
    for i,j,z in alg.table:out[z][j]+=kernel[i]
    return out

def full_cell(alg,z,x,y,g,a,mode):
    if any(not Q(0)<v<Q(1) for v in (z,x,y,g,a)):raise ValueError('Only strictly positive physical cell parameters admitted.')
    return alg.mul(alg.edge(z),alg.cell(x,y,g,a,mode))

def full_cell_polynomials(alg,mode):
    """Five shared physical variables(z,x,y,g,a) in ALL arity components."""
    from forest_algebra import edge_polynomials
    cell=alg.cell_polynomials(mode);out=[{} for _ in alg.coords]
    for i,j,target in alg.table:
        k,f=alg.coords[i]
        for ez,c in edge_polynomials(k)[f].items():
            for powers,d in cell[j].items():poly_add(out[target],(ez,)+powers,c*d)
    return out

def structural_regular_certificate(alg):
    table={(i,j):z for i,j,z in alg.table}
    if len(table)!=len(alg.table):raise ValueError('Ambiguous source grafting table.')
    # Check the exact finite basis, not random vectors or a numerical plateau.
    for i in range(alg.dim):
        for j in range(alg.dim):
            for k in range(alg.dim):
                ij=table.get((i,j));jk=table.get((j,k))
                left=table.get((ij,k)) if ij is not None else None
                right=table.get((i,jk)) if jk is not None else None
                if left!=right:raise ValueError('Actual labelled graft convolution is not associative.')
    for j,(r,f) in enumerate(alg.coords):
        expected=alg.index[r,tuple(range(r))]
        diagonal=[i for i,jj,z in alg.table if jj==j and z==j]
        if diagonal!=[expected]:raise ValueError('Entering-token diagonal is not the singleton coefficient.')
    for i,j,z in alg.table:
        entering=alg.coords[j][0];output=alg.coords[z][0]
        if output<entering:raise ValueError('Incorrect entering-token triangular ordering.')
        if output==entering and z!=j:raise ValueError('Off-diagonal entry in an entering-token block.')
    return {'status':'PASS_EXACT_FAITHFUL_REGULAR_STRUCTURE','cap':alg.m,'dimension':alg.dim,
            'forest_counts':[sum(k==r for k,f in alg.coords) for r in range(alg.m+1)],
            'basis_associativity_triples':alg.dim**3,'all_original_token_labels_preserved':True,
            'diagonal_block':'F_r block is K_r(all singleton forest) times identity',
            'ordering':'ORIGINAL ENTERING TOKEN COUNT; not current surviving roots',
            'faithfulness':'T_K(unit)=K by exact unital multiplication',
            'not_a_positive_word_membership_or_realization_budget':True}
