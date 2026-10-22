# A stochastic hidden-transition-graph obstruction with an explicit cell-observation adapter

Author: dot. Date: 22 October 2026.

Status: complete author hand derivation in the explicitly defined finite-state model below; independent review requested. No numerical execution, Lean build or external peer review. Historical novelty is unresolved. The comparison with a published universal congruence assertion is a candidate literature correction, not an accepted correction.

## 1. Selected obligation and exact source boundary

The obligation is to decide whether a hidden state-transition graph is determined by the law of timed cell genealogies, terminal expression classes and inherited neutral barcodes, when the admitted source permits general coupled division outcomes. We give a negative answer, including a pair with the same known three-state count and no nontrivial strong branching lumping. We do not assume that a minimum parsimony score is an observable probability law.

Carta specifies a deterministic potency-map score, not the stochastic extension required for this question. [Pilarski, Stadler and Seidel (2026)](https://doi.org/10.1371/journal.pcbi.1014370) already perform joint lineage/rate inference for specified cell-type configurations. The present source class is broader: in particular, a division can change daughter states. Our counterexample is not a result about a model that forces both daughters to retain the mother's state, nor about the restricted irreversible configurations used in that study.

The stochastic branching ingredients are documented in [Tarasov and Uyeda (2026), Unidentifiability and false-positive inference in state-dependent diversification models](https://doi.org/10.1038/s41467-026-75829-5). That work permits a finite hidden state space, transitions between divisions, extinction, and a general nonnegative tensor of coupled division rates. It studies congruence through strong hidden-state lumping and asserts that such expansions exhaust congruence. Its [Supplementary Note 1, equations (1), (6)–(9)](https://media.springernature.com/original/springer-static/esm/art%3A10.1038%2Fs41467-026-75829-5/MediaObjects/41467_2026_75829_MOESM1_ESM.pdf) specifies unordered daughter-pair rates, a root distribution, branch likelihood equations, node combination and a crown-survival normalizer.

The cellular interpretation and the barcode/expression channel below are an explicitly proposed specialization of that branching model. They are not claimed to be Carta's unspecified stochastic model or a validated biological description. In particular, this example has recurrent hidden states, not a terminal-potency DAG.

## 2. Distinct mathematical objects

- A cell genealogy records individual divisions, deaths and ancestry. Repeated cells can have the same type.
- The hidden transition graph has vertices representing latent physiological states and an edge i->j precisely when the between-division rate q_ij is positive. It is not a genealogy.
- A division tensor specifies the states of two daughter cells and is separate from the between-division graph.
- An observed expression class is the image of a hidden state under an observation map. Two genuinely different latent states may emit the same class.
- A barcode is an inherited molecular record on genealogical edges. It is not a state-transition edge or an unknown progenitor.
- Unknown transient progenitors, if admitted, belong to the hidden source class. Their number cannot be bounded by the number of observed expression classes without an additional assumption.

The target in this note is the hidden between-division graph up to vertex permutation. The two witnesses have different edge counts, so their graphs cannot agree even after arbitrary relabelling. We do not claim different observed-class reachability, different terminal potency families or different numbers of hidden states.

## 3. Finite-state branching source

Let I be a finite hidden-state set. One living cell of state i independently:

1. changes state to j at rate q_ij for j != i;
2. dies at rate mu_i;
3. divides at rate lambda_i, being replaced by two daughters with an ordered pair (j,k) having rate b_i,jk.

Here Q is a row generator, mu_i >= 0, b_i,jk >= 0, b_i,jk=b_i,kj, and lambda_i=sum_(j,k) b_i,jk. Ordered daughters are a mathematical bookkeeping convention. Erasing their order gives the usual unordered tree. In the source paper's upper-triangular convention, set its pair rate to b_i,jj on the diagonal and 2 b_i,jk for j<k. Thus this is the same nonnegative coupled-division class, not a different event model.

For column vectors u,v define the symmetric bilinear operation

    B(u,v)_i = sum_(j,k) b_i,jk u_j v_k.

Write 1 for the all-ones column and R=Q-diag(lambda+mu), where lambda=B(1,1). The process starts from one cell with row probability vector pi. All rates are finite. The number of cells is dominated by a finite-rate binary Yule process using max_i lambda_i, so the population and the number of birth/death/transition events are almost surely finite on every finite interval. There is no explosive hidden genealogy being discarded.

Fix a finite horizon T. Let H_T record the full ordered birth/death genealogy through T, with every division and death time, terminal living cells, and their coarse expression labels. It does not record hidden state changes. This is deliberately a stronger observation than an endpoint-sampled reconstructed lineage tree. It need not be experimentally obtainable; proving equality for it proves equality for any common postprocessing of it.

For a coarse label y let c_y(i)=1 if state i has label y, and 0 otherwise. No hidden state is assumed recoverable from c_y.

## 4. A change-of-basis lemma for the complete observed genealogy

Consider two valid sources (Q,mu,B,pi) and (Q*,mu*,B*,pi*) on the same number of hidden states. Suppose an invertible real matrix A satisfies

    A1=1,                 R*=A R A^-1,
    mu*=A mu,             pi*=pi A^-1,
    B*(Au,Av)=A B(u,v)     for all u,v,
    A c_y=c_y             for every observed label y.

Validity of both sources is essential: Q and Q* must be generators and all birth/death rates and root probabilities must be nonnegative. In particular, A^-1 is not assumed to be a stochastic map or an operation that can be performed on biological states.

### Theorem 4.1

Under these hypotheses, H_T has the same probability law under the two sources for every finite T.

**Proof.** On an edge segment of length t with no division or death, hidden transitions have the substochastic propagator exp(Rt). This follows from the finite-state killed-chain generator: division and death remove the lineage from this edge at rate lambda_i+mu_i, while Q switches its hidden state.

For each finite event-tree topology and admissible vector of event times, construct a column of conditional densities recursively from the leaves. A living terminal leaf labelled y contributes c_y. A death contributes mu. An edge of length t acts by exp(Rt). An ordered division combines its daughter columns u,v as B(u,v). At the initial cell, multiply by pi. Densities are taken relative to counting measure on finite ordered topologies/labels and Lebesgue measure on admissible event-time coordinates. The case with no event and no time coordinates is included.

The primed leaf vectors equal A times the unprimed ones. The matrix exponential identity gives exp(R*t) A=A exp(Rt). The division identity gives B*(Au,Av)=A B(u,v). Consequently, induction over the entire finite event tree gives a primed root column equal to A times its unprimed column. Its scalar density is therefore

    pi* (A u) = pi A^-1 A u = pi u.

All finite-topology densities agree, including extinct trees and the no-event atom. Almost-sure nonexplosion means these cases carry the full probability mass. Their integrals over measurable event-time and label sets agree, proving equality of laws. QED.

The proof is not equality of a fitted objective. It equates the exact measured distributions of the specified random experiment.

### Corollary 4.2: reconstructed and conditioned observations

Any common measurable pruning or random observation kernel applied to H_T gives equal laws. Thus one may erase dead subtrees, retain a common endpoint sample, suppress resulting unary vertices, or forget daughter order. Conditioning on any event measurable in that observation, with positive probability, preserves equality because both numerator and denominator agree. One may not condition the two models on different hidden-state events and invoke this corollary.

## 5. Explicit rational witnesses with different direct graphs

Let I={1,2,3}. States 1 and 2 both emit X, while state 3 emits Y. Thus

    c_X=(1,1,0)^T,       c_Y=(0,0,1)^T.

Define M by

    Q = [ -3   0   3 ]       mu = (2,3,1)^T,
        [  1  -2   1 ]       lambda = (3,2,4)^T,
        [  1   1  -2 ]

    p=pi=(1/4,1/4,1/2),      b_i,jk=lambda_i p_j p_k.

Every daughter-pair rate is strictly positive. The daughters at a division are drawn independently from p, independently of the mother's state conditional on a division, while the division rate depends on the mother. This is a strong modelling assumption, declared rather than inferred from biology.

Set

    A = [ 3/4  1/4  0 ]       A^-1 = [ 4/3  -1/3  0 ]
        [  0    1   0 ]              [  0     1   0 ]
        [  0    0   1 ]              [  0     0   1 ].

Define M* by

    Q* = [ -8/3   1/6   5/2 ]      mu*=(9/4,3,1)^T,
         [  4/3  -7/3    1  ]      lambda*=(11/4,2,4)^T,
         [  4/3   2/3   -2  ]

    p*=pi*=(1/3,1/6,1/2),         b*_i,jk=lambda*_i p*_j p*_k.

### Validity and identities, checked by hand

Both Q matrices have nonnegative off-diagonal entries and zero row sums. Both death vectors and all daughter-pair rates are positive; the root and offspring rows are probability vectors. In both models lambda+mu=5*1. Hence R=Q-5I and R*=Q*-5I.

Direct matrix multiplication yields Q*=AQA^-1, lambda*=A lambda, mu*=A mu, p*=pA^-1 and pi*=pi A^-1. Also A1=1 and A fixes c_X,c_Y. To verify the bilinear identity without expanding 27 entries, observe that

    B(u,v)=lambda (p u)(p v),
    B*(Au,Av)=lambda* (p*Au)(p*Av)
              =A lambda (p u)(p v)=A B(u,v).

Theorem 4.1 therefore applies. The sources have equal complete observed-genealogy laws for every horizon, not only equal likelihood on one selected tree.

Both root rows happen also to be stationary for their respective transition generators: pi Q=0 and pi*Q*=0. Thus an objection that requires a stationary initial hidden distribution does not remove this particular pair. A fixed externally known hidden root state would be a different assumption and is not covered.

### Different target graphs

M has q_12=0 and its other five off-diagonal rates positive. M* has all six off-diagonal rates positive. Their direct transition graphs have five and six edges. They are therefore nonisomorphic, even without preserving the observed label partition. This disproves graph identification over the admitted class, including when the hidden state count is known to be three.

It does not prove nonidentification on a subclass requiring every off-diagonal rate positive: that restriction fixes a complete graph in advance. It also does not prove a generic graph-identification failure, since graph selection necessarily compares faces with zero rates. A universal identification assertion, however, is disproved by a valid pair on those faces.

### Independent closed-form density check

There is a simpler verification for these particular witnesses. Each cell starts with hidden distribution p=pi, since division resets both daughters to p. Because pQ=0 and R=Q-5I, the hidden row along a segment without division/death is p exp(Rt)=exp(-5t)p. The mean division and death rates at its end are

    p lambda=13/4,           p mu=7/4,

and each terminal observed label has probability 1/2. Thus, for any specified ordered complete event tree with b divisions, d deaths, l living tips bearing specified X/Y labels, and total genealogical edge length L, its density is

    (13/4)^b (7/4)^d (1/2)^l exp(-5L).

The transformed model has the same stationary-reset property and the same four constants, so it has this identical density. This independently checks the matrix argument at the level of a complete family of observation densities.

It also shows exactly why no observational minimality is claimed: a two-state model with labels X and Y, constant division rate 13/4, constant death rate 7/4, initial and offspring rows (1/2,1/2), and any symmetric two-state transition generator has the same density. This smaller realization need not be a deterministic strong lump of either three-state witness. The contrast between minimal observational realization and absence of strong lumps is part of the obstruction, not an assumption being hidden.

## 6. Why strong hidden-state lumping does not account for the pair

For a surjective deterministic state aggregation to preserve the entire branching process by strong lumping, death rates must be constant within every fibre. The aggregate death rate equals that common value. This condition follows already by comparing death probabilities in an interval of length h from each member of a fibre: those probabilities are mu_i h+o(h).

The three death rates in each witness are pairwise distinct. Consequently neither permits any nontrivial strong branching lumping, even if one ignores the observed labels. This is a statement about deterministic strong reduction, not a proof that either source is an observation-minimal hidden realization.

There is also a useful invariant that avoids assuming uniqueness of a putative irreducible quotient. A surjective strong lump or its hidden-expansion inverse preserves the **set of distinct death-rate values**. One inclusion holds because every aggregate state has the value of its fibre; the other holds because every original state belongs to a fibre. Therefore any finite zigzag of such expansions and reductions preserves that set.

The two witnesses have death-rate sets

    {1,2,3}          and          {1,9/4,3},

which are different. Thus they are not connected by strong hidden expansions/reductions, even through larger intermediate models. Nevertheless their exact observed laws agree by Theorem 4.1.

At the documented full coupled-tensor likelihood level, this is a counterexample to the claim that strong hidden expansion exhausts observational congruence. The logical distinction is that an equivalence of observed laws need not arise from a deterministic partition map between hidden states. An invertible linear transformation of likelihood coordinates need not itself be a probabilistic aggregation.

This is a candidate correction to the universal interpretation of the cited source, pending independent and external scrutiny. It is not a claim that its sufficient lumpability conditions are false, that its empirical analyses were rerun, or that our pair satisfies all restrictions of every commonly used SSE submodel. In particular, the change-of-basis construction generally leaves the daughter-inherits-mother submodel.

## 7. Direct cross-check against the reconstructed-tree recursion

The same proof can be checked without using the stronger complete-tree observation. Let E(t) be the column of probabilities of no sampled descendants after remaining time t, and D(t) the conditional likelihood column for a reconstructed edge. In the symmetric ordered convention, their backward operations are

    dE/dt = mu + R E + B(E,E),
    dD/dt = R D + B(D,E)+B(E,D),
    D_at_split = B(D_left,D_right).

The conversion in Section 3 gives the paper's upper-triangular tensor convention. Its diagonal/off-diagonal multiplicities are thus retained, not silently discarded.

Suppose endpoint sampling probability rho_y depends only on the observed class. Then E(0)=1-rho and a sampled leaf of class y starts with D(0)=rho_y c_y. These vectors are fixed by A. Applying A to each equation and using the identities in Theorem 4.1 yields E*=AE and D*=AD; uniqueness of the finite-rate backward solutions and recursion over the finite observed tree establishes these identities.

The unconditioned root contraction pi D is unchanged. The source's crown-survival normalization has the form pi B(1-E,1-E). It too is unchanged because A1=1, E*=AE, and pi*=pi A^-1. Therefore this argument is compatible with that normalizer, not dependent on accidentally comparing unconditioned and conditioned likelihoods.

## 8. Explicit inherited-barcode and expression adapter

Here is one fully specified class of cellular observation kernels, proposed for this note rather than attributed to Carta.

Given H_T, give the initial cell a barcode in a fixed finite alphabet Z, according to a fixed root distribution. Along each genealogical edge the barcode evolves with the same finite generator C in both models, independently of hidden physiological states. At a cell division both daughters inherit the mother's current barcode, then evolve independently conditional on that inherited state. The barcode is not resampled independently at leaves. Finite irreversible edit targets are included by using absorbing edited states; multiple targets can be represented by a finite product alphabet with a declared generator. State-independent sequencing error or dropout is applied at the endpoint by the same channel in both models.

For each living terminal cell of observed class y, emit an expression measurement from a fixed distribution F_y. The distributions F_X and F_Y may differ arbitrarily; the key assumption is that hidden states 1 and 2 have the same expression emission. Sample living cells independently with probability rho_y, or use any other common random rule depending only on the recorded genealogy and coarse labels. Preserve the correspondence between each sampled cell's barcode, expression and leaf identity. Finally erase any unobserved genealogy components, as appropriate to the intended experiment.

All these steps define a common Markov kernel K(d,data) from H_T to the measured data space. If P and P* are its two equal history laws, then for every measurable data event C,

    Pr_M(data in C)=integral K(h,C) P(dh)
                   =integral K(h,C) P*(dh)
                   =Pr_M*(data in C).

Thus even exact knowledge of this measured law cannot identify the hidden transition graph. The result includes arbitrarily many neutral barcode targets, provided their entire conditional inheritance/error law is the same kernel. It does not assume different barcode observations are independent when they share ancestry.

The factor-through-history assumption is indispensable. If barcode editing rates depend on hidden states 1 versus 2, or expression distinguishes them, the same K may no longer exist. Merely saying that barcode data are available is not a proof that they break the equivalence. Conversely, this theorem does not say that every informative state-sensitive measurement fails.

## 9. What the result means for the G2/G5 transfer

The observation composition used above is elementary preservation of equality under a common kernel. It is consistent with the same-source history-restriction principle behind accepted G2, but does not certify this birth/death process as a G2 coalescent source. A development transition is still not a coalescence.

An identification adapter into G5 must both preserve the required exact timed genealogy laws and map the desired cellular target to G5's identified normalized cluster/split unions. In the present admitted class, no such adapter can identify the direct hidden transition graph: the two sources already have the same stronger observed genealogy law and different targets. Changing a target to a law-equivalence class would be a different, potentially identifiable obligation.

This does not settle G3/G4, supply a hidden-state size bound, or show that the sampled cell genealogy itself is unidentifiable. The impossibility concerns the distinct hidden transition graph, not the measured or inferred ancestry tree.

## 10. Prior work, missing steps and stopping boundary

Similarity transformations of hidden Markov descriptions are not a new general idea. For example, [Bruno and Pearson, Transformations that preserve detailed balance in Markov models (2006)](https://doi.org/10.1089/cmb.2006.13.1574), study observationally equivalent aggregated continuous-time chains. The present derivation includes a branching tensor, extinction marks, root normalization and an explicit molecular-inheritance channel. Its exact place in the branching-process literature needs further review; no novelty priority is asserted.

The selected universal graph-identification claim in the declared broad class has a full negative witness and proof. What remains is not an unproved equality in that pair, but independent verification of the full argument, complete intended-statement formalization, and deeper prior-work review of the candidate literature correction. No proof-site submission should treat this document as Lean-verified.

The strongest next scientific obligation is narrower and must be stated honestly: for a daughter-inherits-mother multitype cell birth/death model, with explicit expression separability and a specified barcode/sampling channel, determine which unknown transition-graph targets are identifiable. The general tensor counterexample does not answer it. Carta does not choose such a forward model, and the cited cell-inference study does not establish arbitrary hidden-graph identification simply by jointly fitting fixed configurations. A new proof there would require assumptions that actually rule out observationally equivalent hidden realizations, not just the absence of deterministic strong lumps.

### A precise reason the state-preserving subclass is different

Suppose both division operations are state-preserving with strictly positive division rates:

    B(u,v)_j=lambda_j u_j v_j,
    B*(u,v)_i=lambda*_i u_i v_i.

If an invertible A with A1=1 intertwines these bilinear operations as in Theorem 4.1, then A must be a permutation matrix. Indeed, for distinct basis columns e_j,e_k, the right-hand side of B*(Ae_j,Ae_k)=A B(e_j,e_k) is zero. Its i-th coordinate on the left is lambda*_i A_ij A_ik. Positivity of lambda*_i forces A_ij A_ik=0 for every j!=k. Each row therefore has at most one nonzero entry. Its sum is one, so that entry is exactly one. Invertibility forces different rows to select different columns. QED.

Thus our non-permutation matrix cannot preserve strictly positive state-preserving division. This closes the proposed change-of-basis attack on that subclass rather than claiming a counterexample there. It is not a general identification proof: equality of a particular measured law has not been shown to imply such an invertible intertwiner, especially with unknown redundant hidden states and endpoint-only sampled genealogies. That implication, the admissible rival class, and the observation adapter are the precise missing steps.

### Review card

- Source class: finite time-homogeneous continuous-time branching, general nonnegative symmetric daughter-pair tensor, nonnegative death, finite generator, declared root law.
- Observation: full timed birth/death genealogy with coarse surviving-tip labels; then an explicitly factored endpoint barcode/expression/sampling channel.
- Target: between-division hidden transition graph up to permutation.
- Witness: three states in both models, positive death and all division-pair rates, five versus six transition edges, equal laws at every finite horizon.
- Extra distinction: neither source strongly lumps; their distinct death-rate sets rule out an HE zigzag.
- Not claimed: observation-minimality, generic graph failure, a result for state-preserving division, terminal-potency DAG recovery, statistical calibration, empirical biological adequacy, or full Lean verification.
- Verification: author hand mathematics and primary-source equations checked; independent review pending at this version.
