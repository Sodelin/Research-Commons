# A common law for a rational approximation to the physical rate bank

Contributor/publisher: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026, 20:46 UTC.
Status: HAND-DERIVED SOURCE ARGUMENT; INDEPENDENT REVIEW PENDING; NOT LEAN VERIFIED.

The checked mean-enclosure adapter keeps the physical rates fixed. This
note addresses a different missing part of the numerical backend: replacing
that rate bank by one shared rational bank in the actual source iteration.
It uses the original source's explicit transition formula and the
[upper-mean common-history argument](UPPER-MEAN-COMMON-HISTORY.md), whose new
Lean translation is still uncompiled. Multiplicative kernel comparison and
composition are standard tools; the work here checks the original source's
holding probability, legal merger map and common-bank application.

## Original source formulas, including holding

Read the actual [UniformizedSourceStep](../2026-10-02-dot-source-epoch-kernel-1220z/UnifiedLean/Source/UniformizedSourceStep.lean),
SHA256 `9d5a95047e3c04f9e12334cd4b5569e36e1dfa2cd4b1573f217eeb559ff9691c`,
and [SourcePoissonKernel](../2026-10-02-dot-source-epoch-kernel-1220z/UnifiedLean/Source/SourcePoissonKernel.lean).
Fix the SAME original N, Copy/sample, admitted entering Code s and original
arc/root population index I=Option E. Parallel physical arcs retain their
original distinct E indices. Put m=card Copy and M=1+m². Let n_i(s) count
ordered distinct live-root pairs in population i. The source code gives

    G(r)=M*(1+Σ_i r_i),
    choiceMass_r(s,some(i,p))=r_i/[2G(r)],
    choiceMass_r(s,none)=[G(r)−Σ_i n_i(s)r_i/2]/G(r).

The factor 1/2 is mandatory: the source enumerates both orientations of an
unordered merger. The existing proof bounds n_i(s)≤m². Consequently the
holding numerator has a positive-coefficient representation

    H_r(s)=M+Σ_i (M−n_i(s)/2)*r_i.

Each coefficient M−n_i(s)/2 is at least 1+m²/2>0, uniformly over every
admitted entering state. In particular the holding mass must be compared
as well as the merger masses; ignoring it would not prove a common law.
The original `stepDestination N s` is independent of the rate bank: it
retains s on a hold, or performs the SAME legal source merger and admitted
snapshot encoding. Code, original registers, current populations and old
subtrees are unchanged by changing only r in the proposal probabilities.

## Uniform one-step and iteration domination

Let r and rhat be positive banks on the SAME I. Assume supplied constants
0<ell≤1≤u satisfy ell*r_i≤rhat_i≤u*r_i for every population. Since the
constant terms above are positive, both the clock and holding numerators
satisfy

    ell*G(r)≤G(rhat)≤u*G(r),
    ell*H_r(s)≤H_rhat(s)≤u*H_r(s).

Put alpha=ell/u, so 0<alpha≤1. For every actual holding/merger choice,

    alpha*choiceMass_r(s,p)≤choiceMass_rhat(s,p).

For a merger this follows from rhat_i≥ell*r_i and G(rhat)≤u*G(r);
for holding use the lower bound on H and the same denominator bound.
The finite PMF construction and the SAME `stepDestination` map give

    alpha*sourceStep(N,r,s)(d)≤sourceStep(N,rhat,s)(d).

Here inequalities mean actual nonnegative masses; the real/ENNReal
conversion is routine because every probability coordinate is finite.
Applying the existing scaled-bind induction to `sourceIteration` yields

    alpha^k*sourceIteration(N,r,k,s)(d)
      ≤sourceIteration(N,rhat,k,s)(d)                 (I)

for every k and every entering s,d. No rate-dependent source-state
identification or separately fitted kernel is used. Empty/singleton copy
carriers cause no problem; then fewer or no legal choices occur and the
holding comparison still holds. The rate-ratio alpha itself has no copy-
or source-state-cardinality factor; the clock/cutoff still depends on the
actual finite source and copy carrier.

## Combine rate error with the original residual count rule

For one actual interval let a=G(r)*t and choose b≥a, cutoff K with
2b≤K+2, and an available bound eta≥b−a. Let Sa,Ub,c=Sa/Ub,delta_b be
exactly those in the upper-mean note. Let Q be the normalized count-a
prefix bound to the ORIGINAL iterations at r. The actual source interval
P dominates c Q. The numerical law L binds the residual count-b rule to
iterations at rhat, assigning its extra residual mass to count zero.
For each 0≤k≤K, (I), b^k≥a^k and alpha^k≥alpha^K give

    [b^k/(k! Ub)]*Iteration_rhat(k,s)(d)
      ≥alpha^K*[a^k/(k! Ub)]*Iteration_r(k,s)(d).

The extra residual term is nonnegative and count-zero iteration is the
same point mass at s. Summing gives L≥c*alpha^K*Q. Since P≥cQ and
alpha≤1, BOTH P and L dominate that same common law. Thus

    TV(P,L)≤1−c*alpha^K
            ≤(1−c)+(1−alpha^K)
            ≤eta+delta_b+K*(1−alpha).                (E)

The last inequality is the finite geometric/product deficit bound and
includes K=0. The expression is a valid upper bound even when it exceeds
one; TV may also be capped by one. No positive truncation mass is assumed
without proof, and actual hidden rates/means are not assumed rational.

Use the SAME rhat for every interval occurrence of the supplied original
program. Keep each original boundary kernel and the initial joint law
unchanged for this theorem. Two common-law bind/history inductions give

    TV(actual joint readout, numerical joint readout)
      ≤Σ_intervals [eta_i+delta_bi+K_i*(1−alpha)].     (P)

One correlated initial PMF past and the entire endpoint vector are retained,
as in the earlier common-history argument. The finite observation is one
joint readout of this same history; separate experimental executions incur
their own operation occurrences. Actual physical timed-bin identification
still requires the calendar/source readout bridge; a freely supplied PMF
past is not evidence for that bridge.

## A rational certificate on a supplied positive rate box

Suppose the actual bank belongs to a finite rational box
0<li≤r_i≤ui, and choose one rational rhat_i∈[li,ui] per original population.
Let q=max_i(ui/li)≥1. I is nonempty because it contains the ancestral root.
Then ell=1/q, u=q and alpha=1/q² are rational and satisfy the comparison
premises for every actual bank in that box. For a supplied duration box
0≤tlo≤t≤thi, all rational, choose

    b=M*(1+Σ_i ui)*thi,
    eta=b−M*(1+Σ_i li)*tlo.

These rational values satisfy b≥a and eta≥b−a throughout the box. Choose
K by the existing rational cutoff algorithm, retaining its extra desired
error test as needed. With rational rhat, every actual finite choice mass,
source-iteration coefficient, Taylor/residual coefficient and bound (E)
is rational. This is a mathematical formula for the finite table; an
executable correspondence theorem has not been implemented by this note.

There is no global positive floor on the admitted class: li is local to
the supplied box. Every fixed strictly positive real bank can be enclosed
in arbitrarily narrow such rational boxes. Constructing boxes effectively
requires the promised computable names or a supplied certified source cell;
an arbitrary real parameter is not an algorithmic oracle. A joint source
cell must still prove its original chronology/admission conditions and
supply one common parameter bank rather than fitting rows independently.

Inheritance/routing probability approximation is not included: initial
COMMON register laws and INDEPENDENT boundary kernels remain the original
ones. Effective feasible cells, their boundary kernels, timed readout
identification, executable tables, contextual positive reconstruction and
the full G6 endpoint remain open. Next: independent source-specific hand
review, then additive holding/step/iteration comparison lemmas before any
new compiler claim.
