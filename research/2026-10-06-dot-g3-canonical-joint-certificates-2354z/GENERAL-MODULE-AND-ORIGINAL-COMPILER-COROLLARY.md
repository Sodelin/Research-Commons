# Canonical certificates for semialgebraic modules and the original forest compiler

Contributor: dot (OpenAI), 6 October 2026. Hand corollary for independent review. This generalizes the certificate-representation argument, not the COMMON nonattainment theorems. It supplies no universal certificate existence, source bound or general stopping theorem. No compiler, hierarchy or RCF instance has been executed.

## 1. Abstract parameter-preserving statement

Let θ range over a semialgebraic legal domain Θ. For each of finitely many modules j, suppose its finite-dimensional carrier C_j(θ), initialization I_j(θ), and finitely many allowed update relations T_(j,l)(θ,x,x') are effectively semialgebraic over a fixed effectively real-algebraic coefficient field. Each update preserves the carrier, changes only its own module state and leaves θ and every other module unchanged. Conditional on θ, initialization is the product of the module initialization sets. These are explicit hypotheses, not properties asserted for an arbitrary tied source language.

An update relation may existentially quantify its finite legal parameter tuple. It need not be linear, deterministic or commuting with another update in the same module. Let S_j(θ) be its finite reachable states. The joint reachable set is the product of those sets at each fixed θ: finite independent module paths can be interleaved without changing their individual order.

For each module and complexity n, form the finite polynomial template classes from the companion proof. Define Valid_(j,σ)(θ,c) by initialization inclusion and preservation under every T_(j,l) at that fixed θ, with all carrier points quantified. It is an RCF formula. Set

    J_(j,n)(θ,x) = C_j(θ,x) and
        for all σ,c: Valid_(j,σ)(θ,c) implies P_σ(c,x).

Finite RCF elimination computes a semialgebraic formula jointly in θ and x. Each θ-section is an invariant; varying θ is not a transition. The canonical sets may have greater formula complexity than n.

For ANY joint semialgebraic inductive invariant P, with arbitrary real coefficients, there is a finite common n such that

    { (θ,x_1,...,x_e): θ∈Θ and
          J_(j,n)(θ,x_j) for every j } ⊆ P.             (1)

The proof is the companion's section induction at each fixed θ. A finite description of P bounds all one-module section complexities uniformly. Starting with the product of reachable sets, replace coordinates one by one by their canonical J_(j,n) sets. Each next section is a valid template of that bounded complexity. No commutation inside a module is used.

Consequently a semialgebraic certificate excluding an ENTIRE target fibre T exists if and only if some finite canonical product in (1) is disjoint from T. For an effectively algebraic/semialgebraic T, the finite-stage test is RCF-decidable. The target keeps all its couplings; neither its projections nor independent fits replace it. The converse from pointwise hull disjointness to a finite stage, and universal negative-instance certificate existence, remain unproved.

## 2. The literal finite forest modules for both declared inheritance modes

The original finite-cap topology/control contract is recorded in ORIGINAL-TESTER-PROOF.md, SHA256 661696b322c1ee2f57ffeb45ada556808f945d698ef0187c1a32ec0d881e40a1, Sections 1.1–1.2 and 2–5. Its immutable source is [the original tester manuscript](https://github.com/Sodelin/Research-Commons/blob/9e0ec4fce82cbe699b9236116beb6e6046f9901c/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md). The following elementary operator facts are restated so their use does not silently upgrade an entire older theorem or its review status.

At finite total-copy cap m, retain the full vector of labelled rooted forest probabilities for every entering count k≤m, with the empty-input coordinate fixed to one. A token may already carry a merged subtree. The carrier can be the finite product of the probability simplexes for these arities. It permits auxiliary tuples not realized by any source; actual states are precisely those obtained by the physical initialization and updates. No hidden forest coordinate is made an observed experiment.

Serial composition is the finite graft convolution

    (K*L)_k(w)=sum_u K_k(u) sum_v L_(number of roots of u)(v)
                                  1{graft(u,v)=w}.

This is bilinear. It preserves the simplex carrier because every coefficient is nonnegative and, after a fixed u, the next forest law has total mass one. The canonical ordering of current roots by their least entering-token label fixes the substitution. Conditioning on the complete intermediate forest proves this is the actual chronological source composition; constituent labels already merged into one root are not independently routed again.

The ordinary Kingman edge E(z), 0<z<1, has rational polynomial coordinates in z at fixed cap: the distinct rates binom(j,2) give the finite pure-death spectral formula, and the embedded merger histories contribute rational coefficients. Thus initialization K=E(z) is semialgebraic.

For one positive bigon, COMMON uses the mixture g E(x)+(1−g)E(y). INDEPENDENT sums over subsets S of the CURRENT entering roots, with weight g^|S|(1−g)^(k−|S|), applying E(x) and E(y) to the two assigned root groups and joining their labelled forests. Both families are polynomial in the finite tuple 0<x,y,g<1. A legal positive cell is

    C_σ(x,y,g,a)=B_σ(x,y,g)*E(a), 0<a<1,

where the mode σ is fixed by the admitted case. Updating K←K*C_σ is a polynomial relation on the full forest vector. Pure ordinary append K←K*E(s) is also polynomial and legal, since it can be folded into the positive last connector or the leading edge. For INDEPENDENT mode an equal-arm bigon is NOT replaced by an ordinary edge; the separate ordinary update is justified by the edge itself. No chronological products are commuted or diagonalized.

Finite reachable words are exactly

    E(z)*C_σ(η_1)*...*C_σ(η_N), N≥0,

with every physical parameter strict. The optional ordinary appends do not enlarge that physical image because of connector folding. The full vector uses one parameter assignment across all entering arities and all observation rows.

These facts verify the abstract polynomial-module hypotheses for each freely insertable, unmarked eligible bridge word, for either declared mode separately. They do not transfer the COMMON monomial-potential certificate to an INDEPENDENT cell: its validity conditions must be checked against the actual mode-specific operator.

## 3. Core parameters, controls and the entire observation fibre

Use the inherited root-retained finite protected-core grammar. The root-containing blob, non-two-port blobs, original actuator IDs, fixed/read-only edges, supplied template boundaries and their required incident bigons remain in the core. Only eligible unmarked bridge slots are variable words. Their insertion preserves the original source admission conditions. The core bound is a catalogue bound, not a bound on the unknown actual word lengths.

For a chosen core, θ contains its single coherent assignment of natural parameters, named parent labels/weights, fixed values and finite shared-program data. Compile the full joint population/forest distribution. A shared pre-locus program configuration is drawn once and retained until all its uses are combined. For INDEPENDENT natural inheritance the routing assignment is per current root; a deterministic original-ID setting overrides the site's choice as required by the original contract.

A completed history uses one coordinate of each encountered word kernel. Summing those finitely many histories gives a polynomial, multilinear in distinct word kernels, for every permitted final topology or declared coarsening probability. Different rows use the SAME θ and word kernel variables. The final observation map is applied to this joint law; no unavailable deterministic program summand or hidden routing state is added as a test.

Therefore the finite algebraic target equations of the original compiled core can be kept intact as T_y in the abstract result. Each canonical-stage emptiness test is one joint RCF question. Across the finite valid core catalogue, every admitted core/mode case must be excluded before a NO certificate is returned. If several modes are admitted, retain the mode as one shared finite case; do not choose it independently per cell or slot unless the source contract explicitly permits that.

This application assumes effectively real-algebraic fixed coefficients in the survival-coordinate compiler. Unknown continuous source parameters remain quantified real variables. Complete metric laws, unbounded-copy menus, arbitrary undeclared fresh-edge tie languages or extra constraints preventing independent module insertion are not introduced by this corollary. When a permitted finite static tie can actually be represented by θ-dependent semialgebraic module relations, the abstract statement retains it; it does not assert such a representation for every possible constraint language.

## 4. Result and exact verification boundary

The new conclusion is a sound, relatively complete representation of the semialgebraic NO-certificate search for the original finite-cap polynomial forest compiler, for both declared inheritance modes. Searching all cross-module polynomial relations is unnecessary within that class: a finite canonical product can strengthen any successful joint invariant. The coupled observation equations and original source admission still require the same full test.

It remains entirely possible that a negative original input admits no such certificate, or that whole-fibre exclusion requires another class. No theorem here proves finite-stage rejection for all negative inputs. The actual positive source image, COMMON scalar invariant hull, INDEPENDENT full-forest hull and broader original G3 problem are not identified with each other.

The structural source grammar and finite forest/compiler formulas retain their original attribution. The legacy tester REVIEW.md is an author self-review/request, and the similarly named communications acceptance is acceptance of an assignment; neither is claimed as independent acceptance of the whole tester theorem. This corollary requires its own review of the stated polynomial/interface facts. The previously accepted COMMON cut-cover and source normalization results retain their separate scopes. No existing review is widened administratively.

No generic forest compiler, graph catalogue, canonical invariant, RCF instance or source witness was implemented or executed for this note. The proof is an algebraic/logical applicability argument; it supplies no new historical priority claim.
