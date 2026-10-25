# Zero-entry extension of the conditional boundary-invisibility gate

Author: dot (OpenAI), 25 October 2026. Written proof candidate with bounded exact controls. Not yet coordinator-reviewed. This extends BOUNDARY-INVISIBILITY-GATE.md without changing that reviewed file. It does not extend the complete known-entry reconstruction theorem to arbitrary zero-entry epochs.

## Statement

Retain the coherent all-old-tuple response interface, positive rates, finite constant migration, independent routing, fixed source-faithful old-name mixture H, and local-invisibility definition from BOUNDARY-INVISIBILITY-GATE.md. Drop the assumption that every new Gamma column has positive sum.

Then local invisibility implies:

1. Exactly a new demes are directly populated by Gamma.
2. Gamma is a deterministic bijection from the a old demes onto those directly populated new demes.
3. No migration leaves that set of a demes during the next constant epoch.
4. On that closed set, the pulled-back new generator and coalescence rates equal the old ones, in the same coordinate frame.

The converse holds. Additional new demes may exist, but they are unreachable from this entry throughout the declared next constant epoch and do not affect its genealogy law. They are not automatically globally irrelevant: a later boundary or later rate change might make them reachable. Only the restricted local statement is asserted.

## 1. The first two star coefficients count directly occupied states

Uniform old-coordinate averaging gives product entry p_i = (1/a) sum_u Gamma_ui. Let S={i:p_i>0}; no positivity is imposed outside S. Set x_i=p_i mu_i for i in S.

For k>=2 let a_k be the specified labelled k-star density with all waiting times at their right limit zero, and let b_k be its derivative in the first waiting time, with the subsequent waits at zero. For the killed k-lineage generator K and pure-state terminal factor v_k(i,...,i)=mu_i^(k-1), these are alpha v_k and alpha K v_k. The same direct computation as the prior first-derivative proof gives

    a_k = sum_(i in S) p_i x_i^(k-1),
    b_k = k sum_(i in S) (pR)_i x_i^(k-1)
          - choose(k,2) sum_(i in S) x_i^k.

Here (pR)_i uses the full generator, including negative diagonal contributions for migration out to zero-entry states. There is no assumption that its sum over S vanishes.

Why no missing zero-entry terms? A terminal pure state in a zero-entry deme cannot be reached by one migration from an initially supported configuration when k>=2. Directly, its usual formula terms contain x_i^(k-1)=0. Migration from occupied states into a zero-entry deme contributes through the diagonal departure term and is correctly retained in pR on S. No division by zero p_i is used.

Set a_1=1 as the known total mass, not as a zero-dimensional merger density. The positive moments a_k identify the finite measure sum_(i in S) p_i delta_(x_i). Let its distinct positive support be X. Then

    b_k/k = sum_(x in X) x^(k-1) [U_x - (k-1) m_x x/2],
    U_x = sum_(i in S:x_i=x) (pR)_i,
    m_x = number of i in S with x_i=x.

Confluent Vandermonde uniqueness for the independent sequences x^(k-1) and (k-1)x^(k-1) identifies m_x. Thus the number of directly occupied states |S|=sum_x m_x is identified from these first two coefficient families, even though zero-entry states and their rates have not been reconstructed.

The invisible no-boundary comparison has uniform entry on precisely a old demes. Equality of these coefficient families therefore forces |S|=a. This argument uses only the earlier coefficient formula, not a silently extended positive-entry identification theorem.

## 2. Routing is a bijection onto S

For distinct old labels, the initial pair-coalescence density is zero in the no-boundary comparison. Positivity and the fixed H mixture force pairwise disjoint supports of all Gamma rows, as in the reviewed gate. There are a nonempty disjoint row supports and precisely |S|=a supported columns. Hence Gamma is a deterministic bijection onto S. Its other columns are zero.

Pull the directly populated new states back to old names through this bijection. For each positive-weight hidden alignment h, denote their coalescence rates by nu_i^h and generator entries among them by M_ij^h. Let r_i^h be the TOTAL departure rate from i, including departures to zero-entry states. H acts on old names coherently, not independently for each statistic.

## 3. Detect leakage to zero-entry states

Initial same-class pair densities and the joint densities of two disjoint such pairs identify E[nu_i^h] and E[(nu_i^h)^2]. Invisibility makes these lambda_i and lambda_i^2, so nu_i^h=lambda_i in every positive-weight component.

For an initial same-class pair, the derivative at zero of its first-coalescence density is

    g_i,h'(0) = -(nu_i^h)^2 - 2 nu_i^h r_i^h.

There are two independent possible lineage departures. A single departure leaves the lineages separated and cannot contribute an instantaneous coalescence in the new state; therefore no off-diagonal arrival contribution enters this derivative. Invisibility and already-fixed nu give E[r_i^h]=sum_(j!=i) Q_ij.

The directional triad probe initially (j,j,i), with its two prescribed sequential mergers, gives E[M_ij^h lambda_j^2]. Dividing by lambda_j^2>0 yields E[M_ij^h]=Q_ij for every distinct directly populated pair i,j. Subtracting these active-state exit rates from the total gives

    E[ sum_(g outside S) R_(h(i),g) ] = 0.

Every term and every mixture weight is nonnegative. Hence each direct-state-to-ghost rate vanishes in every positive-weight component. In particular the actual new source has no migration from S to its complement. No state outside S can then be reached during this constant epoch, even via several migration steps.

Finally, two disjoint directed triad probes give the corresponding second moments. As in the reviewed gate, their variances vanish and every M_ij^h=Q_ij. Thus the active restriction is the unchanged old epoch in the correct frame. Diagonal equality now includes the established absence of ghost leakage.

## 4. Interpretation and limits

The hidden-state count need not literally be unchanged if unused states are admitted as representation artifacts. The correct local statement is equality on the entry-reachable closed set, plus possibly unreachable extra states. A zero-entry state that becomes reachable by migration in this same constant epoch cannot be hidden by a locally invisible boundary under the acquired interface.

This does not identify all parameters of an arbitrary reachable-zero-entry epoch when the boundary is visible. The full next-epoch induction still needs that more general supplier or a precisely restricted source class. Nor does this prove that the required coherent interface is obtainable at an unknown boundary, or solve arbitrary-history termination.

The proof reuses the prior star coefficient and coherent probe methods. Its proposed incremental result is the removal of the directly-populated-column assumption from the conditional invisibility classification, not a new general theory of hidden-state minimality.

## Executed controls

check_zero_entry_gate.py uses exact fractions for three demes, p=(2/5,3/5,0), rates (3,2,17), and migration rows (-7,2,5), (3,-10,7), (11,13,-24). Both positive-entry x values coincide at 6/5. It checks a_k and b_k for k=2,...,7 including nonzero migration to the zero-entry deme. It also checks the initial pair-density derivatives -51 and -44 and recovers ghost exit rates 5 and 7 by subtracting active exit from total exit. The script exited zero; zero-entry-control.json is its unedited output. This is a bounded algebraic control, not verification of the general theorem or any empirical model.
