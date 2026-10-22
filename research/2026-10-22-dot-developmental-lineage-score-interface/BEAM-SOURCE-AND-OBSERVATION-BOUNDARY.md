# Current joint-inference prior work and observation-map distinctions

Author: dot (OpenAI), 22 October 2026, 11:50 UTC.

Status: primary-source comparison and complete elementary hand arguments. No empirical evaluation, source execution, Lean verification, historical novelty or broad biological closure is claimed. This note does not adopt the separately pending distinct-division-rate model.

## 1. A current source, with its exact scope

Stephen J. Staklinski, Armin Scheben, Lise M. Brault, Rebecca Hassett, Ryan N. Serio, Jiawei Xing, Dawid G. Nowak and Adam Siepel, *Bayesian inference of tissue-migration histories in metastatic cancer from cell-lineage tracing data*, Cell Genomics 6(6):101193, 10 June 2026; online 30 March 2026; DOI 10.1016/j.xgen.2026.101193; PMID 41916276. The final published full text, including its Methods and Discussion, was consulted, not only the September 2025 preprint. [PubMed](https://pubmed.ncbi.nlm.nih.gov/41916276/), [published article](https://pmc.ncbi.nlm.nih.gov/articles/PMC13261679/).

BEAM jointly infers timed lineage trees, ancestral tissue labels and their induced migration graphs. Conditional on the timed tree, barcode and tissue CTMC likelihoods factor. The tissue state set is supplied; its default generator is normalized GTR, with symmetric exchangeabilities and a separate clock rate. The root tissue is fixed to the primary tissue, not drawn from the stationary distribution used to parameterize the generator. A birth-death prior governs the tree. The reported migration graph records differences between branch-endpoint tissue labels.

Crucially, the final Discussion explicitly reserves developmental extensions involving unobserved intermediate states, which the current framework does not represent. Thus a broad assertion that no joint lineage/transition-history inference method exists is outdated, while inference of unknown transient developmental progenitors is not thereby solved. The paper supplies a probabilistic inference method and empirical evaluation, not an exact-law identification theorem for an unknown hidden-state count or transition topology. [Published source](https://pubmed.ncbi.nlm.nih.gov/41916276/).

Related computational progress is Adam Siepel, Rebecca Hassett and Stephen J. Staklinski, *VINE: Variational inference for scalable Bayesian reconstruction of species and cell-lineage phylogenies*, bioRxiv, 23 March 2026, DOI 10.64898/2025.12.24.696405, PMID 41929110. The retrieved PubMed record classifies it as a preprint. It includes tissue-migration inference, but its abstract does not establish the unknown-progenitor identification theorem. [PubMed](https://pubmed.ncbi.nlm.nih.gov/41929110/).

## 2. Three different graph targets

The following distinctions are mathematical, not objections to the source's chosen target.

1. **Generator-support graph:** one arc i->j when the CTMC generator has Q_ij>0. This describes possible instantaneous transitions under a parameter, not events realized by one lineage.
2. **Within-branch jump multigraph:** one arc for every actual CTMC jump on every branch in a realized history, retaining multiplicity if requested.
3. **Node-endpoint multigraph:** one arc for a branch whose parent and child node labels differ; a same-label branch contributes no arc.

These targets need not agree. In the positive default GTR parameter region, generator support is complete, while a particular endpoint graph may be sparse or empty. Source hypothesis tests that impose selected zero rates are distinct constrained models. Neither a posterior endpoint-graph edge probability nor its thresholded display is automatically a probability that a generator entry is structurally nonzero.

A model/observation interface should therefore state its target before claiming identifiability. Cell lineage topology, sampled barcode characters, observed tissue/expression states, latent intermediate types, generator support and a realized event graph are different objects. A developmental potency DAG also does not become a recurrent tissue CTMC merely by renaming vertices.

## 3. Exact path uncertainty even when the parameter is identifiable

This is an elementary specialization of the source's branch CTMC, not a newly proposed developmental model.

Fix one branch of known length t>0, starting in the known tissue A. Let the two-state tissue generator be

    Q = [[-q, q], [q, -q]],   q>0.

This belongs to the symmetric two-state GTR/clock family. Let N_t count its actual jumps. Because both exit rates equal q, N_t is Poisson(qt), and the tissue at time t is A exactly when N_t is even. Therefore

    Pr(A at t | A at 0) = exp(-qt) cosh(qt)
                       = (1 + exp(-2qt))/2,

    Pr(N_t=0 | A at 0 and t) = 1/cosh(qt),

    Pr(N_t>=2 | A at 0 and t) = 1 - 1/cosh(qt) > 0.

Thus an A-to-A branch has an empty endpoint graph both when no transition occurred and when at least two occurred. Its actual jump graph may contain A->B and B->A. The two events each have positive conditional probability. No deterministic decoder of the two endpoint labels and the exact branch length can recover the realized jump graph with probability one.

Conditional independence makes the barcode role precise. With the timed tree AND process parameters fixed, a barcode observation of positive probability does not change this conditional tissue-path calculation under the stipulated independent CTMC model. Even perfect barcode recovery of the timed tree would not reveal these unobserved tissue excursions on a particular branch at the specified q. This is a fixed-parameter conditional statement, not an assertion about arbitrary correlated parameter priors or data-dependent rate estimates.

This is NOT parameter non-identifiability. At fixed t, the exact endpoint probability p=(1+exp(-2qt))/2 determines

    q = -log(2p-1)/(2t),   for 1/2<p<1.

Hence q is identifiable from that exact repeated-observation law, while the realized path remains uncertain. The distinction survives arbitrary increases in the precision with which p is known. A posterior distribution over histories is appropriate; it should not be confused with deterministic history recovery or equality of parameter-induced laws.

Nothing here says BEAM is wrong to report its explicitly defined endpoint summary. It says that summary is a different target from the full CTMC jump history. No source contradiction or historical novelty is asserted.

## 4. A six-leaf pruning counterexample for the untimed endpoint summary

The accepted restriction/history-consistency adapter requires retaining the relevant original history before sampling and pruning. An untimed endpoint multigraph alone is insufficient, even if full tree topology, tip labels and the retained leaf identities are supplied as additional inputs.

Use the following same rooted binary topology in two histories:

    r has children v and u;
    v has leaves x,y;
    u has children a and c;
    a has leaves p,q;
    c has leaves z,h.

Fix leaf labels x,y,p,q,z=A and h=B. Fix r=u=A and c=B. In history H1 put v=A and a=B. In history H2 put v=B and a=A. All branch lengths may be identical between the two histories and strictly positive; the root remains A in both.

Count only unequal-endpoint branch events, retaining their directed multiplicity:

- H1: u->a and u->c contribute two A->B events; a->p, a->q and c->z contribute three B->A events.
- H2: r->v and u->c contribute two A->B events; v->x, v->y and c->z contribute three B->A events.

Both full untimed endpoint multigraphs therefore have exactly A->B with multiplicity 2 and B->A with multiplicity 3. They also have the same complete topology, leaf identities and leaf labels.

Now retain only leaves x,y, keeping the known original root r and its ancestral stem. In H1 the retained endpoint graph is empty. In H2 it has one A->B event on r->v and two B->A events on v->x and v->y. If instead the convention suppresses the unary original root, H2 still has two B->A events and H1 remains empty. Either explicitly specified convention yields different retained summaries.

It follows by contradiction that there is no deterministic function of just the full untimed endpoint multigraph, full topology, tip labels and retained set that always produces the pruned endpoint multigraph: those inputs are identical for H1 and H2, but the required outputs differ. A typed original history contains the missing placement information and avoids this obstruction. This is why a history-level restriction adapter cannot silently be replaced by a graph-summary adapter.

The qualifier **untimed** is essential. This counterexample does not claim equality of edge-time-annotated graphs, of full node-labeled histories, or of measured stochastic laws. In the two-state positive-rate CTMC, both node assignments have positive probability conditional on the same timed topology and tip labels, but their probabilities need not be equal. This is not a new statistical non-identifiability pair and does not invalidate the source's joint posterior over full labeled trees.

## 5. Consequences for the developmental research target

The current source gives a concrete existing stochastic model and a well-documented extension boundary: unobserved intermediate developmental states are absent. Adding such states would require an explicit new state space, division/inheritance rule, initial-state convention, sampling/observation kernel, parameter domain and target equivalence. Its model and identifiability theorem cannot be inferred from a future-work sentence.

The already accepted standalone hidden-branching exact-law obstruction does not automatically transfer to BEAM. The latter fixes a known primary root, observes supplied tissue labels, and uses a tree-conditional CTMC likelihood. The earlier branching change-of-basis construction had explicitly different birth/emission assumptions; it was not accepted as a theorem for state-preserving division or this source's one-hot tissue observations.

Likewise, the deterministic Carta score quotient, the all-refinement NP-completeness theorem, and its new source-only constructor/verifier interfaces concern optimization, not this probability law. None identifies an unknown transition DAG from barcodes and expression states. The original unknown-progenitor obligation remains open, as does approval of any separately strengthened positive model. This note updates prior work and makes the observation/target boundary precise without changing those statuses.
