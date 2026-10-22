# Unknown conserved total: an exact identification dichotomy

Author: dot (OpenAI). Date: 22 October 2026 UTC.
Status: complete author-checked hand proof; scoped coordinating hand-review PASS on 22 October 2026.
Formal verification: not performed. Novelty: unresolved.

## 1. Primary model and the changed nuisance contract

The underlying model remains the monomial mass-action chemical Langevin reaction diffusion used by [Faul, Hoessly and Xia](https://doi.org/10.1017/S0956792526100382), restricted to the unit-conversion class in [the controlled-total theorem](PARTIAL-OBSERVATION-TOTAL-PANEL.md):

    P(a,b)=sum p_ij a^i b^j,  p_ij>=0,  i>=1;
    Q(a,b)=sum q_ij a^i b^j,  q_ij>=0,  j>=1.

P is the total A-to-B intensity and Q the total B-to-A intensity. The source is finite, nonempty, and has no duplicate source/direction reactions. The graph and all active rates are unknown. No molecularity bound is needed.

This note changes one assumption deliberately. The observed initial concentration A_0=a_0 is known, but the hidden initial concentration B_0=C-a_0 is an unknown positive deterministic nuisance parameter. Thus the conserved total C is unknown. It is not a random mixture over totals. Every individual candidate source/initial-state pair still induces a scalar Markov diffusion after using its own deterministic conservation relation.

Fix one common, known interval I=(l,u), with 0<l<a_0<u. Admit only candidates with C>u. Stop the observed A at first exit from I and hold it at the reached endpoint. The observation is either its exact continuous stopped path law on any fixed positive horizon, or its exact joint stopped law at fixed times Delta,2 Delta under the already specified monitored stop/hold protocol. The rival uses the same a_0, I, time units, labels, observation times, and stopping rule. Its hidden initial concentration is allowed to differ because that is the nuisance now under study.

This is a natural specialization of the partial-species-observation direction, not the identical-full-initial-state comparison in the paper's Definition 3.2. A distinction between these two contracts is essential: the theorem below is not a further counterexample to that original definition.

## 2. The entire one-experiment fibre

For a source/total triple (P,Q,C), define the univariate restrictions

    p_C(x)=P(x,C-x),
    q_C(x)=Q(x,C-x).

The observed scalar drift and variance are q_C-p_C and p_C+q_C, respectively. They are smooth with positive variance on the closure of I.

**Proposition 1 (unknown-total fibre).** Two admitted triples (P,Q,C) and (P',Q',C') have equal prescribed observations if and only if

    P(x,C-x)=P'(x,C'-x),
    Q(x,C-x)=Q'(x,C'-x)

as identities of univariate polynomials in x.

**Proof.** The continuous-law coefficient-extraction lemma, or the separately proved two-time killed-kernel theorem, recovers drift and variance throughout I. Their half-sum and half-difference recover p_C and q_C there. Polynomial identity extends equality from I to the whole real line. Conversely, the polynomial identities give equal scalar coefficients on I and hence equal stopped laws. QED.

Thus the observation determines two univariate polynomials exactly, but does not automatically determine their bivariate source or the total. Polynomial extrapolation here is a consequence of exact law equality and the model class, not a numerical claim about estimating remote roots from noisy observations.

## 3. Exact total-identification dichotomy

**Theorem 2.** Within the admitted class of unknown graphs, rates, and deterministic hidden initial concentrations, the total C is identifiable from one prescribed experiment if and only if Q is nonzero.

More explicitly:

1. If Q is nonzero, C is the smallest strictly positive real zero of the recovered polynomial q_C. Every rival with the same observation has C'=C.
2. If Q is zero, for every C' with u<C'<C there is an admitted rival with total C', the same observation, and molecularity no larger than the target's. The total is therefore not even locally identifiable in this class.

**Proof of (1).** Because every term of Q contains b and Q is nonzero,

    q_C(C)=Q(C,0)=0.

For every 0<x<C, both x and C-x are strictly positive. Each active monomial of Q is then strictly positive, and all coefficients are nonnegative. Hence q_C(x)>0 throughout (0,C). Thus C is exactly the first strictly positive root. A possible root at x=0 is irrelevant to this statement.

Any observationally equivalent rival has q_{C'}'=q_C by Proposition 1. This polynomial is nonzero, so the rival's Q' is nonzero: a nonzero nonnegative polynomial cannot vanish on the positive line segment. Applying the same first-positive-root argument to the rival gives C'=C.

**Proof of (2).** Fix u<C'<C and put delta=C-C'>0. Define one rival source by

    P'(a,b)=P(a,b+delta),
    Q'(a,b)=0.

Binomial expansion preserves nonnegative coefficients and finite support. Every monomial still contains a, so every term corresponds to an admitted A-to-B unit-transfer reaction. The total degree cannot increase. The polynomial remains nonzero. Treat coincident expanded monomials as one reaction with the summed positive rate.

At the rival total,

    P'(x,C'-x)=P(x,C'-x+delta)=P(x,C-x),
    Q'(x,C'-x)=Q(x,C-x)=0.

The initial observed concentration is still a_0; the rival hidden initial concentration is C'-a_0>0. Both sources remain in the positive quadrant over the common stopped interval because C,C'>u. Proposition 1 proves equality of the actual stopped observations. Taking arbitrarily small delta>0 proves nonidentifiability arbitrarily close in total; the translated coefficient vectors also converge to the target coefficients in the common degree-bounded ambient coefficient space. QED.

The direction-presence condition is itself visible in the exact observation: q_C is identically zero if and only if Q is absent. This exact zero test is not a claim of robust finite-sample branch selection.

## 4. One common rival can match a relative-offset panel

The negative branch is not an artifact of fitting each experiment separately.

**Corollary 3 (shared-source offset ambiguity).** Suppose finitely many experiments share one unknown base total C and known additive offsets eta_j. Experiment j has known observed initial concentration a_j, total C_j=C+eta_j, and a common-to-target-and-rival observed stopping interval I_j=(l_j,u_j) containing a_j. Assume C_j>u_j for every j. All experiments use the same fixed source and rates. If Q=0, no such finite relative-offset panel identifies the base total C over the admitted class.

**Proof.** Choose one delta satisfying

    0<delta<min_j(C+eta_j-u_j).

Use the single rival source P'(a,b)=P(a,b+delta), Q'=0 in every experiment, and the single rival base total C'=C-delta. The rival experiment totals are C'+eta_j=C_j-delta, so all the known offsets are preserved. For every row,

    P'(x,C'+eta_j-x)=P(x,C+eta_j-x).

All positivity and stopping conditions remain valid. Proposition 1 gives equality in every experiment using this one shared rival and one shared rate assignment. QED.

For Q nonzero, any one experiment already identifies its absolute total and therefore the base total after subtracting its known offset. That does not automatically identify the graph/rates from that one experiment.

## 5. Total identification is not network identification

Even when Q is nonzero and C is recovered, the known-total fibre can still contain different reaction graphs and rates. For any fixed C>0, compare

    P_0(a,b)=a,         Q_0(a,b)=b,
    P_1(a,b)=a(a+b)/C,  Q_1(a,b)=b.

Both sources have nonnegative admissible coefficients and at least one reverse reaction. On a+b=C they have identical P and Q restrictions. Therefore they share the observed stopped law at this total. The first has a unimolecular forward reaction; the second has two bimolecular forward reactions. The total is identifiable, while the forward graph is not.

Conversely, the negative total ambiguity can persist even on a fixed supplied graph. With

    P(a,b)=k_1 a+k_2 ab,   Q=0,   k_1,k_2>0,

the change C'=C-delta is matched by k_1'=k_1+k_2 delta and k_2'=k_2. The same two-reaction graph and positive rates remain admitted. This is a graph-preserving example, not a claim that every fixed graph has the same nuisance ambiguity.

## 6. What measurements break the displayed ambiguity

Knowing B_0 in one experiment, together with the already known A_0, anchors the absolute total and excludes the shifted rivals. The same is true of one direct calibrated measurement of A_t+B_t before the stop. If any reverse reaction is present, the exact observed law already anchors the total through the root argument, without observing B directly.

After the total is anchored, graph/rate recovery still needs an adequate experiment panel or additional structural information. The controlled-total G4 theorem supplies one such all-rival panel under its explicit assumptions. Merely adding more experiments with only known relative offsets does not anchor the absolute total in the one-way branch, even though the same source is used throughout.

These conclusions preserve calibrated labels and units. They do not permit changing the observed A units, the clock, or the known offsets. The countermodels shift only the unknown hidden initial concentration and compensate through permitted reaction coefficients.

## 7. Attribution, relation to G4, and remaining scope

The use of conservation laws, source restrictions, polynomial identities, and positivity is not claimed as historically new. The main continuous and sampled scalar lemmas are separately attributed in the companion proofs. The result here is an explicit nuisance-sensitive specialization, with novelty unresolved.

[Cinquemani (2018), Identifiability and Reconstruction of Biochemical Reaction Networks from Population Snapshot Data](https://www.mdpi.com/2227-9717/6/9/136), Section 3, explicitly includes unknown initial moments as additional parameters in an affine-reaction, population-moment framework. Unknown initial conditions as an identifiability nuisance are therefore prior work, not a newly proposed issue. The present result concerns an exact global dichotomy for the displayed nonlinear diffusion class and exact stopped-law observation contract.

No new G theorem is invoked in this dichotomy. It identifies when the known-total input needed by the G4 molecularity adapter can be inferred from the observation, and when a real shared-source ambiguity prevents inferring it. Invoking a finite-dimensional rank theorem would not remove this exact ambiguity.

Random hidden initial totals, several unreconstructed hidden species, non-unit reaction vectors, unknown observation scales, non-Markov observed processes, and finite-precision/finite-sample inference remain outside the theorem. In particular, replacing the unknown deterministic C by a distribution over C changes the scalar Markov property and invalidates the present coefficient extraction without a new argument.

Scoped coordinating hand-review PASS was completed on 22 October 2026, conditional on the separately reviewed scalar extraction and two-time theorems. The review checked the first-positive-root characterization, translation preserving admitted nonnegative coefficients and degree, common nuisance/stopping contract, and one shared rival across all relative-offset experiments. It did not certify historical novelty or Lean verification. No statistical estimator or full solution to the paper's general partial-observation direction is claimed.
