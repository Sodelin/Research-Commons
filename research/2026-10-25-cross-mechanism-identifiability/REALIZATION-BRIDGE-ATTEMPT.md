# Sample-consistent realization: rigidity lemma and a real obstruction

Author: dot (OpenAI), 25 October 2026. Status: written elementary lemma and obstruction, not independently reviewed or Lean checked. The all-panel cross-mechanism master remains open. Classical matrix intertwining, tensor products and symmetry averaging are reused; no historical novelty is asserted.

## Useful result first

A single stochastic map that respects both migration and the two-lineage no-coalescence process cannot smear one deme into several demes: positive coalescence forces a deterministic injection, and reachability then forces a permutation. However, observationally valid, deletion-consistent realization maps need not be tensor powers of one map. In fact, individually minimizing the one-lineage and two-lineage observable processes already destroys the tensor structure needed for the rigidity argument.

Thus the next serious problem is an **observable-to-multiplicative-realization bridge**, not another proof assuming the hidden populations are available to the observer.

## 1. Conditional two-lineage rigidity lemma

Let source and target epoch deme sets have sizes d and e. Let Q and R be finite continuous-time Markov generators, with row-vector convention. Coalescence rates lambda_i and mu_j are strictly positive. On ordered uncoalesced lineage pairs define

    D_lambda[(i,k),(i,k)] = 1_{i=k} lambda_i,
    K_lambda = Q tensor I_d + I_d tensor Q - D_lambda,

and define D_mu, K_mu analogously using R. These K matrices are killed generators: loss of mass means a coalescence occurred. Migration paths and deme names remain hidden.

Suppose a d-by-e nonnegative row-stochastic matrix T satisfies

    Q T = T R,
    K_lambda (T tensor T) = (T tensor T) K_mu.

Then there is an injection f from source demes to target demes such that

    T[i,j] = 1_{j=f(i)},
    mu_{f(i)} = lambda_i.

The image of f is closed under target migration. If every target deme is reachable from initial distributions of the form alpha T, then f is onto and T is a permutation matrix. Migration generators are then permutation-conjugate. This is an algebraic implication, not a claim that the hypotheses follow from gene genealogies.

### Proof

The one-lineage intertwining gives

    (Q tensor I + I tensor Q)(T tensor T)
      = (T tensor T)(R tensor I + I tensor R).

Subtracting the killed-generator identity yields

    D_lambda(T tensor T) = (T tensor T)D_mu.

Its entry indexed by source pair (i,k) and target pair (j,l) is

    lambda_i 1_{i=k} T[i,j]T[k,l]
      = mu_j 1_{j=l} T[i,j]T[k,l].

For k=i and j != l, positivity of lambda_i forces T[i,j]T[i,l]=0. Each stochastic row is therefore supported on exactly one entry, equal to one. Call its position f(i). For i != k and j=l=f(i)=f(k), the same identity would give 0=mu_j, impossible. Hence f is injective. Taking i=k and j=l=f(i) proves rate equality.

For any target j outside the image, (QT)[i,j]=0 whereas (TR)[i,j]=R[f(i),j]. Thus R[f(i),j]=0. The image is closed. All initial distributions alpha T are supported in it, so target reachability forces the image to be the entire target deme set. QED.

No full-rank assumption, distinct-rate assumption or ability to prepare individual hidden demes was used **inside this implication**. Nonetheless supplying a T with these two identities is a strong hidden-level hypothesis; removing it is the main research obligation.

## 2. Why projectivity is not the missing proof

Take two hidden demes, identical positive coalescence rate lambda, and symmetric migration rate m>0. Let P exchange the deme names and P_n=P tensor ... tensor P on n ordered current lineages. Define

    F_n = (I + P_n)/2.

Each F_n is stochastic. It commutes with the n-lineage migration and killed generators because global deme exchange leaves migration and same-deme pair hazards unchanged. For the operator C_ab merging labelled lineages a,b when they occupy the same deme, symmetry gives

    F_n C_ab = C_ab F_{n-1}.

If D deletes one lineage's deme coordinate, then F_n D = D F_{n-1}. Thus the family respects label permutations, sampling deletion, hidden dynamics and observable coalescence transitions. Uniform independent entry routing alpha_n=(1/2,1/2) tensor ... tensor (1/2,1/2) satisfies alpha_n F_n=alpha_n. An eventual deterministic merge into one root deme also respects the symmetry. Consequently this example can occur in an admitted independently routed positive-duration history; no common biological routing coin is required.

But F_1 has every entry 1/2, so F_1 tensor F_1 sends a fixed ordered pair to all four ordered pairs with probability 1/4. F_2 instead sends that pair only to itself and its global swap, each with probability 1/2. Therefore

    F_2 != F_1 tensor F_1.

The averaging is an algebraic transformation of hidden descriptions, not a new demographic event. This does not prove two nonisomorphic biological mechanisms have equal laws, and it does not disprove existence of some tensor-compatible equivalence map (the identity exists here). It refutes the proposed inference that deletion consistency plus observable intertwining automatically makes an arbitrary such family a tensor power.

## 3. Even panel-by-panel minimal realization is insufficient

In that same symmetric epoch, the one-lineage unmarked genealogy records no coalescence and reveals no migration. Its observable survival function is identically one, admitting a one-dimensional minimal representation.

For two lineages independently routed uniformly into the two demes, aggregate their hidden locations into S (same deme) and D (different demes). Before the next fixed epoch boundary the no-coalescence generator and initial law are

    K = [[-(2m+lambda), 2m], [2m, -2m]],
    alpha = [1/2, 1/2].

Let s(t)=alpha exp(Kt) 1. Direct differentiation gives

    s(0)=1,  s'(0)=-lambda/2,  s''(0)=lambda^2/2.

A one-dimensional time-homogeneous linear realization would have s(t)=exp(-ct), hence c=lambda/2 and s''(0)=lambda^2/4, a contradiction for lambda>0. Thus the two-lineage observable process needs at least two linear states even though the one-lineage process needs only one. A finite future deterministic root merge does not alter these derivatives on the epoch's positive-duration interior.

The uniform two-lineage entry law can be supplied by an ordinary independent routing boundary; it need not be experimentally prepared. Conditioning on no observed coalescence before that boundary leaves the two entering lineages in their known preboundary deme, and fresh independent routing supplies the stated law. This is an ordinary observable conditioning event, not access to hidden states.

Therefore constructing a minimal realization separately for each panel and tensoring the n=1 realization cannot recover the biological occupancy structure. A successful master proof needs a coherent cross-panel structure stronger than deletion alone, potentially an extremal or multiplicative reconstruction principle established from legal genealogy observations. Neither the name “minimal realization” nor generic HMM identifiability supplies that principle.

## 4. Exact master-facing next target

Given two complete histories in the declared grammar with identical unmarked timed genealogy laws for every legal finite labelled sample panel, construct compatible hidden-level maps across each observable epoch, or give an admitted counterexample to their existence. The construction must come from legal genealogy cylinder probabilities and their derivatives/conditional laws, not from assumed hidden-state preparation.

Precisely missing suppliers are:

1. Recover or normalize genuinely observable epoch boundaries without assuming the architecture. Completely silent boundaries are excluded from recovery and must be normalized away or retained as an explicit ambiguity.
2. Obtain enough positive separating coalescence-history functionals to distinguish relevant hidden occupancy states, including equal-rate/symmetric cases.
3. Choose coherent maps across panels and show multiplicativity, rather than only marginal/deletion consistency.
4. Apply the lemma to migration epochs, then align boundary routing and fixed sampling labels.
5. Handle unknown finite deme/epoch counts without pretending fixed-candidate comparison gives total recognition.

Failure of item 3 may reveal genuine exact cross-mechanism ambiguity; the symmetric averaging example alone does not. A proof may need to recover the physical state algebra before minimizing observable linear representations. This extends the prior finite-epoch no-migration alignment boundary rather than re-proving its accepted special case.

## 5. Implementable restricted end-to-end benchmark contract

This benchmark is a tool for developing and falsifying the bridge, not a replacement for the all-panel master.

### Biological sources

Implement a finite structured-Kingman simulator and exact small-panel generator for three labelled populations. Compare three explicitly declared families: one independent directional pulse; a positive-duration continuous-migration window between the same demes; and a strictly ancestral-subdivision model with no cross-partition communication after a declared separation time. Use the same fixed divergence scaffold, positive coalescence rates and root absorption. Start with one to two haploid copies per population. Include equal-rate/symmetric parameter controls, not only generic random parameters. Fix the scaffold only for this benchmark.

### Actual observations

For each realized labelled genealogy simulate homogeneous JC finite alignments of a declared length, initially 32 or 128 bases per nonrecombining locus, using one shared calibrated mutation model. Sample L independent loci with specified L; do not call linked blocks independent. Compare raw sequence-pattern counts as the primary observation, with true timed genealogies retained only as an oracle diagnostic. The benchmark's clock and independence are explicit restrictions, not master assumptions.

### Exact and finite-data layers

For small panels, compute pairwise survival/Laplace quantities using finite killed generators and validate the simulator against them. Seek exact algebraic kernel equalities where the encoding supports them; matching floating likelihoods is not exact equivalence. Fit each admitted family jointly to the same simulated sequence data and record confusion, confidence coverage, sensitivity to near-pulse duration and failure to identify parameters. Include simulations generated outside the fitted family, and say exactly which alternatives were omitted.

### Feasible next measurement

Use a finite prespecified menu: additional haploid copies from an existing population, additional independent loci, or longer within-locus alignments. Assign a transparent cost vector (samples, loci, bases), not a fictional universal monetary cost. Use a development set to nominate the most discriminating design against current rival fits; evaluate separation and error on held-out replicates across all benchmark families. Do not claim uniform guarantee if the pulse/migration closure prevents a positive margin. Serial sampling and linked-locus models are later separately specified experiments, not covered by the current simulator contract.

### Reproducible comparison

Record source family/parameters, seeds, observed-data generator, exact checks, fitted alternatives, optimization starts, failures and held-out outputs. Compare model-conditioned best fit with the larger-family ambiguity set at matched observation budgets. A useful endpoint is an honest “not distinguishable under this design” result accompanied by a tested next-measurement recommendation or a quantified obstruction. No benchmark runs are claimed here beyond the separately labelled algebraic controls.

## 6. Prior-work boundaries

Structured-coalescent generator/generating-function calculations are established: Lohse, Harrison and Barton (2011), https://pmc.ncbi.nlm.nih.gov/articles/PMC3213358/ . Do not call their likelihood compilation a new method. The 2014/2017 introgression/structure papers and 2025/2026 linkage studies in MASTER-CONTRACT-AND-FIRST-ATTACK.md remain the main scientific anchors. The conditional rigidity implication is elementary algebra; symmetry averaging is classical. The unresolved scientific/mathematical contribution would be the legal-observation bridge or a source-faithful obstruction across the full admitted families.

No empirical validation, formal proof checking, source-classification algorithm or novel benchmark result is asserted by this document.

## 7. Executed algebra controls

check_realization_obstruction.py was run using Python's exact fractions.Fraction arithmetic, with migration rate m=3 and coalescence rate lambda=2. For n=1,2,3,4 it verified symmetry-map commutation with killed generators and preservation of independent uniform entry laws; for n=2,3,4 it additionally verified deletion and one labelled coalescence-operator intertwining. It verified F_2 differs from F_1 tensor F_1, that the latter fails killed-generator intertwining, and survival derivatives s'(0)=-1 and s''(0)=2 versus the one-state prediction 1. Results are recorded in realization-control.json. These are bounded algebra controls, not a formal theorem certificate or a demographic benchmark run.
