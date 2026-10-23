# P5: complete hand-proof counterexample to the unrestricted comparison

21 October 2026. P5 source-owner mathematical verdict after an end-to-end
adversarial self-audit. The original unrestricted comparison is FALSE for
the admitted bounded-neighborhood class. The result below is a complete
HAND-PROOF claim with an algorithmically specified admitted finite family.
It is not an evaluated large-system witness, a full independently reviewed
paper, a formal Lean certificate or a historical novelty claim.

The earlier files deliberately retained candidate status while their
suppliers were being derived. This verdict adopts the completed derivation
as a hand-proof result: no mathematical supplier remains merely assumed
without a proof in the accompanying packet. Independent and formal
validation retain the narrower evidence levels listed below; they are
not silently relabelled as complete. The separate Lean/native builder's
goals, owners and action-specific holds are unaffected.

## The theorem and exact original scope

Let c=exp(-1/8), b_G=c sqrt(pi/8)exp(-1/128). For every integer ell>=40
fix baseline gamma=1, tau=2^(-ell), and ORIGINAL parameters

 Gamma=9/4, b0=2b_G/9, h=b_G/4,
 j=h/Gamma=b0/2, x=Gamma tau,
 k_max=12, m_max=30, nu_max=30, beta=tau/8.

They satisfy h<b0 Gamma and
x<=1/(12nu_max 2^m_max). There is one FIXED physical observable

 O=X1 Y2 X3

on the SAME three labelled root qubits in every system, with Hermitian
operator norm1. There are finite static-Hamiltonian qubit models, all
three independent thermal bare-Pauli channels at every site, and POSITIVE
normalized initial densities, such that

 sup_(admitted models with these fixed parameters) sup_(s>=0)
   ||[exp(s L_T*)-exp(s R*)]O||op = infinity,
 T=sqrt(tau/Gamma).                                (V1)

L_T is the ORIGINAL square-window generator INCLUDING its ordered Lamb
shift, with the SAME static H and covariances as the original infinite-
filter Redfield generator R. The conclusion is about the original
comparison itself. It is not just nonpositivity, failure of a sufficient
response lemma or a growing initial observable.

More quantitatively, for balanced binary trees with N=2^(q+1)-1 data
vertices, at all sufficiently large depths q, the finite admitted
parameter-grid maximum satisfies

 max_grid |Tr[rho_N exp(s R(r,u,v)*)O]|
                >=exp[y^2 sqrt(N)/55296],          (V2)

y=Jtau>0, J=b_G/32. Its positive densities are fixed once per N, and
the observation times obey0<=s<=N^(-1/2). Thus even times tending to
zero suffice. An unrelated REAL onsite Pauli term pins exact h across
volumes and selected parameters. The geometry may be a bounded-degree
tree; the original contract requires no polynomial ball-growth bound.

## Where each formerly conditional supplier is proved

The readable source export is P5-CONSOLIDATED-REVIEW-PACKET-v2.md,
98839 bytes, SHA256
ddb4d25bba8d7b94a1e77393ca4ecff483b6ac80379923a0f18d6406c76237a4.
All twelve source modules and projection hashes are included. It retains
its earlier candidate-status introduction as a historical snapshot; the
present verdict records the subsequent full author audit and adoption.

1. Actual block amplifier and every-duration clock functional are proved
   in P5-GAUSSIAN-AMPLIFIER-C2-v1.md. The four full-filter transition
   vectors give a negative projection rate, kappa'(0)>=2a0, and the cb
   Taylor derivative bound gives kappa'(s)>=a0 on the entire needed
   interval. Physical Pauli covariances determine all logical coordinates.
   Positive INITIAL mixtures have logical functional norm1 at every
   required duration, with the pure prescribed bit at t_N. No base code
   invariance or positive physical output is assumed.
2. Static reachability and physical geometry are proved in the C4
   interface and P5-C4-PREMISE-AUDIT-v1.md. The finite symmetric-spin
   representation proves the exact binomial law; a centered Bernoulli
   moment bound proves both tail constants and their endpoint offsets.
   The clock gauge comparison treats noncommuting gates in their actual
   order. Its uniform isometry estimate gives prepared operator-norm
   compression. Full eight-dimensional embeddings preserve every term
   norm and commute with H_c, giving exact SAME-H S5 without a projected
   physical model. The isolated term is included exactly once.
3. D3/D5 are proved by the full physical touched-set Dyson expansion in
   CODE-FUNCTIONAL-DYSON-BOUND-v1.md. The packet proves the scalar
   functional's cb norm directly by compression. Outside the union of
   local insertion supports, partial contraction is taken only in the
   independent BASE functional. For ONE global probe, outside factors
   are I before insertion and have one actual post-probe duration.
   Bimodule contraction permits nonlogical touched physical factors.
4. P5-WEAK-LINK-ANALYTIC-SUPPLIER-v1.md proves the absolute weighted
   interaction bound with constant1000 and the global code source bound
   2gamma. Rooted commutators give support<=1+3n and cancel the factorial
   against the exponential series. The finite increment cutoff is fixed
   on the whole analytic r disk; no unsigned infinite-bath expansion is
   used. The long real unitary acts AFTER the local short-time bound.
5. P5-FULL-PROBE-TRANSFER-v1.md proves the actual full-filter comparison,
   with all channel/volume counts. The shifted central pulse matches Q_S
   exactly before tails are estimated. The three derivative Duhamel
   terms give8theta gamma s(1+144M gamma s)exp[300M gamma s-(S/tau)^2].
   The same real r,u and fixed positive rho_N are retained. No actual
   contraction, positive output or discarded delayed pulse is used.
6. I13 in P5-INTERPOLATION-AND-ADMISSION-v1.md derives one FINITE lower
   bound from the four analytic variables. Theta is excluded from the
   r-analytic function and introduced only after selecting real r.
   Exact root conservation at auxiliary u=0 converts that response to
   a time derivative. Explicit time Taylor errors and a polynomial
   derivative bound force a large finite-time response. ONE-probe D5
   bounds the complex root-u disk; finite interpolation returns to
   u>=1. Actual transfer and a v-polynomial derivative bound then force
   a large ORIGINAL prediction. Higher v orders use only the coarse
   global norm. Every remainder and asymptotic exponent is displayed.
7. P5-FINITE-GRID-COROLLARY-v1.md puts all four selected REAL parameters
   on finite grids. The mandatory admission correction restricts the
   search to q>=4ell+80, proving EVERY tested density positive before
   any prediction can count as a witness. The earlier unqualified
   small-q search wording must not be used. This fixes a specification
   omission; the sufficiently-large-N theorem already had the condition.
8. P5-PHYSICAL-BATH-AND-COMPARATOR-ADMISSION-v1.md proves all Gaussian,
   KMS, signed modulation, common-envelope/floor and original parameter
   bindings. It also writes the ORIGINAL square-window dissipator as
   a positive spectral integral of Lindblad dissipators. Its actual
   ordered H_T is Hermitian. Its Hermitian norm-one predictions are
   bounded by1 in the SAME positive initial density, proving V1 from V2.

These are proofs of the needed implications, not numerical extrapolation
from their finite control suites. The exponents separating the limits
are strict at fixed parameters: the full-tail exponent N^(2/3) beats
sqrt(N)log^3 N; the weak-link exponent N^(1/6)log^3 N is smaller than
the r interpolation degree N^(1/4); and all interpolation/physical-delay
losses are o(sqrt(N)), below the positive fixed data-gain coefficient.

## The fully specified admitted sequence

For q>=4ell+80 build the stated clock with fixed epsilon_clock=1/32,
positive data/root inputs and the exact positive clock mixtures based
on t_N=N^(-1/2). Use the finite grids

 r=r_N/2+j r_N/(2m_r), j=0,...,m_r,
 u=1+j/m_u, j=0,...,m_u,
 s=t_N*j/(8N^6), j=0,...,8N^6,
 v=-1+2j/(8N^6), j=0,...,8N^6.

Here r_N=N^(-1/3), m_r=ceil(N^(1/4)) and m_u is the specified certified
integer rounding of sqrt(N)/sqrt(log N). Certified upper rounding of
the clock length avoids any undecidable exact-real ceiling comparison;
the C4 error decreases at those lengths and the proof is unchanged.
For each integer B>=2, dovetail finite-grid prediction precision and
increasing qualified q, stopping only when modulus>B is certified.
V2 proves termination. Require each subsequent returned q larger than
the preceding one. This defines a computable sequence of finite admitted
counterexamples with discrepancy>B-1, without deciding ties in maxima.

Full filters are defined by their original infinite integrals; certified
numerical truncation is only an evaluation tool with the common envelope
tail. The delayed pulse remains until that actual tail licenses its
removal. Exact formulas define the densities; approximate arithmetic
never substitutes an uncertified rounded state. No member of this
physical search has zero root noise, complex parameters or a cutoff bath.
The finite grid has polynomial cardinality, but its matrix evaluation
is exponential in M. Threshold volumes can be astronomical. A tractable
numeric witness is not claimed and no such search was executed.

## Actual verification and precise limits

The complete author audit checked the physical admission, tensor partial
contractions, clock gauge/sector/order, original incidence, complex sharp
conventions, all three Duhamel differences, Cauchy remainder constants,
four distinct analytic-variable uses, fixed-density binding, finite-grid
selection and final ORIGINAL-comparator implication.

Three existing-peer HAND returns independently reviewed bounded parts:

- LEAN-P5-DYSON-AUDIT-07 agrees with D3/D5 under their literal hypotheses.
- LEAN-P5-PROBE-TRANSFER-08 agrees with T4/T7 conditional on its suppliers.
- LEAN-P5-C4-GAUGE-ISOMETRY-09 agrees with gauge/isometry/S5 conditional
  on S3 and exact embeddings.

Their exact exclusions remain in the review ledger. None is a whole-paper
independent acceptance or a new formal theorem. Existing clock/gauge/
geometry and code-leaving/interpolation exact controls passed once. The
NEW admission correction's18 exact rational controls passed, with its
full report encrypted before first persistence. Replays are unnecessary.
These finite checks do not establish V2 by simulation; V2 follows from
the hand argument above. The earlier hosted Lean4.35 algebra/integral
checks concern separate positive-route components and are not claimed
as certification of this counterexample. Native4.33.1/Lake/object custody
and the builder's unbound first writers remain separate.

Full independent review and full formalization have not been performed.
Historical novelty remains unassessed; standard Duhamel, interpolation,
thermal/KMS and engineered-spin-chain ingredients retain their attribution.
Those evidence limits are not replaced by a claim that packet existence,
transport acceptance or a checker startup proves the theorem.

## Outcome for the assigned scientific question

The original P5 question permits a complete proof OR an admitted
counterexample. V1 is the latter, at the explicitly stated hand-proof
level. The unrestricted positive comparison cannot be supplied on the
whole declared geometry class. The missing positive-route gate was the
uniform ACTUAL Redfield response/integrated-influence bound, not a CP
reference; no such positive supplier is asserted here. Instead the
original comparison itself has the admitted negative result above.

Earlier commuting-Pauli results and the restricted chain/ring work retain
their scopes. This is a P5 mathematical outcome only, not closure of
G3/G4/P1/G6/G7, a global Lean package, privacy enforcement or native
execution. The authored sources remain ordinary files outside Git and
no sub-agent or duplicate chat was created.
