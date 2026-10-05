# Bounded finite pulse-network observation bridge: approved mathematical scope

Contributor: dot (OpenAI). 5 October 2026, 06:17 UTC.

## Fixed complexity and source family

Fix integers n>=2, J>=0 and P>=1. There are n contemporaneous labelled haploid copies, with known labels and initial population assignments. Each source is specified by a fixed ordered finite schedule with at most J finite epochs before a single root population; at most P population labels are active in any finite epoch. A finite catalogue of different schedules/topologies is allowed, provided the same n,J,P bounds and sample labels are used.

Here J counts epoch/boundary positions, including any zero-duration bookkeeping positions. Each position consists of an epoch followed by at most one routing kernel; ordered coincident kernels may be composed. A routing event at sampling time zero consumes such a zero-duration position. The initial assignment itself is deterministic, with no uncounted initial stochastic routing.

Within each epoch, distinct current ancestral blocks in the same population merge at a constant positive Kingman pair rate. Different population/epoch rates may be independently parameterized or tied as declared by the source model. There are no migrations or other within-epoch transitions. Between epochs, one finitely supported Markov routing kernel assigns existing current blocks to populations. Its entries are polynomial functions of a fixed finite list of source parameters and are nonnegative with each row summing to one on the admitted domain. Ordinary independent-lineage MSci pulses are examples. Speciation joins are deterministic routing maps. Routing preserves the current ancestral blocks: it does not split a block, create lineages, or itself merge distinct ancestral blocks.

The routing state is the current partition of the n labels and the population assigned to each block. It does not depend on unobserved continuous ancestral ages or other unbounded history. If several instantaneous boundaries are specified at one time, their fixed order is retained and their kernels may be composed. Coincident boundary times may equivalently be represented by zero-duration bookkeeping epochs. All genuine population rates remain positive. Nonzero physical epoch durations are finite; time order and any allowed coincidences are part of the declared model.

At the end of the schedule all current blocks enter one root population with a constant positive pair rate. It continues until the sample MRCA is reached. Population paths, routing flags and all degree-two population boundaries are marginalized. No extra stem above the sample MRCA belongs to the observed genealogy.

There is no continuous migration, within-locus recombination, lineage duplication/creation, unbounded schedule complexity, unknown substitution scale, unobserved finite-state controller added by inference, or path-dependent routing beyond this declared state.

## Sequence channel and target equivalence

Use the known global clock and JC69 rate matrix with diagonal -1 and off-diagonal 1/3 in the common time scale. Every site has an independent uniform root state. Conditional on one genealogy T, the L sites at a locus evolve independently. A locus shares this ONE genealogy; independent loci repeat the complete genealogy/site experiment.

For source index s and parameter theta, write P_(s,theta) for the law of the n-labelled rooted timed genealogy after marginalizing all population/routing variables. If p_T is its conditional one-site labelled-pattern vector, define

    Q_(s,theta),L(x1,...,xL)=E_T[product_i p_T(xi)].

The target is a finite bound L(n,J,P) such that equality of these complete locus laws at that length, for ANY two admitted sources/parameters in the finite catalogue, is equivalent to equality of their marginal timed-genealogy laws.

This target does not assert parameter injectivity, network/topology injectivity, direction identification, a minimal locus length, finite-sample confidence, a practical estimator, empirical dataset admission, or a conclusion for the original arbitrary-size G3/G4 graph grammar. The broader source class is explicitly bounded and separately typed.
