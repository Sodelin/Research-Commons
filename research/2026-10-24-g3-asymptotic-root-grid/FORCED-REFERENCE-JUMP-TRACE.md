# Forced nonlinear trace on the actual commutator fibre

Stable key G3-FORCED-REFERENCE-JUMP-TRACE-01. Existing G3 owner,
24October2026UTC. **PROVED BY HAND at the scope below**, author self-review
complete. Independent correctness review and Lean are absent. No new
scientific/source/coefficient/model/native/solver execution occurred.

This is a receiver extension of the OLD nonlinear jump trace, using the
completed compensated source bounds. It is a component of the existing
full-scope conditional G3 attempt, not a new full attack or an index proof.

## 1. Exact original-source scope and conclusion

Keep the SAME actual equal-arm finite private word, original IDs, fresh
INDEPENDENT choices by CURRENT root, opaque grafts, chronological order and
paired commutator assumptions of COMPENSATED-SOURCE-JUMPS.md. In particular

    c=2^(-1/m), H=-log c<=log2, h=-log t,
    K_COMMON=E(c), b2I(K)=c^(3/4),
    [K_I,S(t)]=0 through the existing complete nine-root carrier,

with the unchanged S(t). All strict coins, relative cell scales, finite
counts and unknown higher diagonals remain unrestricted. Take h below
the fixed threshold for its known reference eigenbasis.

Use the previous notation B_h for the fixed (1,3) reference eigenvector
entry (called B there), so |B_h|<=C*h^2. For the actual chronological
factorization cell_i=exp(tau_i*Q) C_i, put

    q_i=exp(-u_i), 0<u_i<=H,
    r_i=g_i*(1-g_i)*[(2g_i-1)^2*u_i^2+u_i^3],
    T=sum physical ordinary times+sum tau_i=3H/4.

Let b(s) be the normalized first-row six-/nine-root coordinate in the
EXACT reference basis, E_b=integral_0^T b(s)^2 ds. Let Pi be the positive
diagonal propagator, normalized to1 initially:

    Pi'=21Pi on ordinary intervals,
    Pi_i+=(d3_i/d1_i)*Pi_i- at C_i.

The conjugated C_i top-six entry is the EXACT

    Y_i=F_i+B_h*(d1_i-d3_i).

Define its rescaled source step

    J_i=Y_i/(d3_i*Pi_i-).                           (1)

There is a constant C_H independent of h, all coins/scales and finite
count such that

    sum_i |J_i|^(5/2)
      <=C_H*[E_b+|B_h|*T^(1/4)*E_b^(3/4)]
      <=C_H*(E_b+h^8).                             (2)

In particular, the OLD unforced trace proof is not simply applied after
changing basis: the continuous forcing is retained explicitly.

For the OLD bare source f_i in the9/7/6/4 representation, also

    sum_i |f_i|^(5/2)
      <=C_H*[E_b+h^8+h^5*sum_i r_i^(5/2)].          (3)

The last source sum is retained. Neither(2) nor(3) bounds E_b, signs the
compensated balance, or implies V_h, AG-Pair or original G3 termination.

## 2. Prior comparison and exact reuse

The OLD scalar5/2 jump inequality and rescaled-walk argument were already
supplied in the existing G4 workspace:

* NONLINEAR-SOURCE-JUMP-TRACE-R1.md,3647B/
  SHA11b89283c1421bcbffeae8f5bbd1907de03b126ddecf424c081798f39ceba748.
* FAIR-ALL-WEAK-SCALES-CANDIDATE-R7.md,10506B/
  SHA40a255d5e53996236a3a0c6406971cf32373d50fc67825dfe94e8c9c507f9d2b.

Both COMPLETE bodies were read and hash verified. Their mathematics is
REUSED, not a new jump lemma. The former allows biased weak cells in a
fixed interior coin interval and an ordinary returning endpoint. The
latter's full no-return argument retains exact fairness.

The later COMPLETE near-fair R9 source9036B/
SHAd4352b1663f823594ffa797c8e401f1302daf185f988b6b12e6232b0b64d2781
was reread. Its fixed-window ordinary-endpoint theorem is not extended.
The earlier MULTISCALE-STORAGE-BOUND-R1.md4159B/
SHAf32e340e36318fba49dfc96fcee277f3a8776051e89f608c3d66e7945d7021b6
was read COMPLETE; its adjacent-minimum trace is valid, and the nonlinear
successor already addresses that particular trace loss. We do not reopen it.

The immediate public actual-source supplier is
[COMPENSATED-SOURCE-JUMPS.md](https://github.com/Sodelin/Research-Commons/blob/b1fd4801188ccf19e43c04989eddd6b5fd3cfddc/research/2026-10-24-g3-asymptotic-root-grid/COMPENSATED-SOURCE-JUMPS.md),
14724B/SHA794bcb58e93ed33c2075b6176c229875c7235a788e1c5609a3890e4f2dd6e0e0.
Its complete body was read; uniform all-coin source bounds and the fixed
reference basis are reused without any new source coefficient derivation.

Difference in the new use-site: equal arms give uniform exposure control
even at rare coins, and conjugated commutation gives zero b endpoints but
an INHOMOGENEOUS ordinary evolution. The old raw scalar walk is not closed
at that endpoint. Formula(2) keeps the exact forcing correction, then
bounds it by h^8. Relevant local audit/history aliases were searched
before this write; bounded no-hits are not historical novelty or absence.

## 3. Actual positive propagator and own preceding intervals

The diagonal Pi is the current b6/b9 ratio. Reference conjugation does
not change diagonals. At completed source prefixes it is the actual
original prefix ratio. Inside a preceding nominal ordinary interval, it
is that actual prefix followed by positive ordinary duration<=u_i.
Since tau_i<=u_i, this still consumes at most the original COMMON budget.

Original source deletion/no-merger bounds give

    1<=Pi<=c^(-36).                                (4)

This does not call a standalone signed C_i stochastic. The lower bound
uses b6>=b9 for the corresponding positive prefix; the upper uses
b6<=1 and b9>=c^36.

The preceding proof gives tau_i>=3u_i/8 and an ordinary interval before
C_i of length ell_i>=tau_i. The intervals are disjoint and ell_i<=T.
Also d3_i>=2^(-15). The all-coin source estimates imply

    |Y_i|<=C*r_i, r_i<=C*u_i^2,
    sqrt(|J_i|)<=C*u_i.                            (5)

All constants are uniform at g_i->0,1. This is possible because the arms
are equal and u_i<=H; it is not a uniform claim for unequal strong arms
whose rare routing can hide their duration.

The only trace adjustment needed for the forced ordinary dynamics is
elementary. On an interval of length ell, b'=21b-21B_h, so, in backward
time x from its end,

    b(ell-x)=B_h+(b(ell)-B_h)*exp(-21x).

Set a=21ell, y=exp(-21x), then rescale the y interval to[0,1]. The
result is an affine function with endpoint b(ell), and its integral
weight is at least exp(-a). For ANY affine function with endpoints U,V,

    integral_0^1 [U*(1-z)+V*z]^2 dz
       =(U^2+UV+V^2)/3>=V^2/4.

Consequently, without assuming a sign or size for either endpoint,

    integral_interval b^2
       >=(ell/4)*exp(-21ell)*b(ell)^2.

Using ell_i>=3u_i/8 and disjointness gives

    sum_i u_i*(b_i-)^2
       <=(32/3)*exp(21T)*E_b.                      (6)

No post-jump own-scale trace, adjacent-scale ratio or count bound enters.

## 4. The closed forced walk and its exact potential balance

Put z=b/Pi. The exact ordinary equation and propagator give

    z'=-21B_h/Pi.

The exact affine source update and(1) give

    z_i+=z_i-+J_i.

The whole conjugated matrix is diagonal by the actual commutator and
the reference's distinct diagonal eigenvalues. Thus z starts and ends
at0, although the ORIGINAL raw six-/nine-root coordinate need not.
No unknown k_j has been set to a fractional reference power.

Reuse the OLD scalar inequality, valid for all real z,J:

    |J|^(5/2)/4
       <=64*sqrt(|J|)*z^2
          +|z+J|^(5/2)-|z|^(5/2).                 (7)

For completeness its old two-case argument is direct: if |z|<=|J|/4,
the potential gain is at least
[(3/4)^(5/2)-(1/4)^(5/2)]|J|^(5/2)>|J|^(5/2)/4.
Otherwise the mean-value bound, |J|<4|z|, controls the negative
potential change by60*sqrt(|J|)*z^2; the remaining quarter-power term
is at most4*sqrt(|J|)*z^2. This is reuse, not new scalar mathematics.

Sum(7). The jump potentials telescope WITH the continuous potential
change, not alone. With psi(z)=|z|^(5/2), exactly

    sum_i [psi(z_i+)-psi(z_i-)]
       =(105/2)*B_h*integral_0^T
                    Pi^(-1)*z*|z|^(1/2) ds.       (8)

Using(4)-(6),

    sum sqrt(|J_i|)*(z_i-)^2<=C_H*E_b.

Also finite Holder and Pi>=1 give

    absolute value of(8)
       <=C*|B_h|*T^(1/4)*E_b^(3/4).

These prove the first inequality(2). Young's inequality with exponents
4/3 and4 gives

    |B_h|*T^(1/4)*E_b^(3/4)
       <=3E_b/4+|B_h|^4*T/4.

Since B_h=O(h^2), this proves the stated h^8 bound, with T fixed by
the SAME original pair data. E_b=0 causes no division by zero.

## 5. Bare source readout and precise remaining task

The exact old normalization has F_i=exp(36tau_i)*f_i and

    F_i=Y_i-B_h*(d1_i-d3_i).

The source bounds give |d1_i-d3_i|<=C*r_i. Moreover d3_i*Pi_i-
has a uniform upper bound by the same original budget. Therefore

    |f_i|<=C_H*|J_i|+C*h^2*r_i.

Taking powers5/2, summing and applying(2) proves(3). This step does not
replace the retained source residual by a free actuator or claim an
effective fair-coin margin.

The completed trace controls steps in terms of energy. The missing
source argument must control that energy and the SIGNED compensated
errors and b-a contribution on the full chronological fibre. There is
no acquired converse, physical replacement, one-witness selector,
V_h<=C*h^5, phase estimate, bound on word count, unrestricted NO or G3
impossibility. The OLD raw storage boundary remains nonzero where stated.

All prior mathematical source bodies are unchanged. This is HAND proof
and source comparison, not an executed source law or independent/Lean
acceptance. Existing source/menu/register/parent/calendar/graft ownership,
no-local-Git/no-subagent and all scientific/model/native/controller/
held/USED/UNKNOWN/privacy restrictions remain. No new peer job is selected.
