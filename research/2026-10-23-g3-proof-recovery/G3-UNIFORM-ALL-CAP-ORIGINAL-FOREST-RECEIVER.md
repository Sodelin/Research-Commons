> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# G3: one full-forest receiver for arbitrary finite root count and word length

22 October 2026 UTC. Existing G3 owner. The original-source argument below is
HAND and UNCOMPILED. Separate exact symbolic controls actually passed. General
G3 and its terminating unrestricted NO case remain OPEN. No local Git,
subagent, native/compiler/model job or new physical tuple was used.

The user requests a uniform result instead of successive degrees. Distinguish
three integers: m is the CURRENT entering-root count, N is the physical word
length, and d is a polynomial degree. This construction applies to EVERY
finite m,N in one argument. It supplies the full forward kernel, not a cutoff
for the inverse search over unknown N. The fixed octic arithmetic obstruction
is a separate promised subproblem, not a size limit on original G3.

## Reused numerical source and the new source-facing claim

The retained forest_algebra.py already constructs arbitrary finite-cap ordinary
and bigon forest rows. Its source is Commons07c9a510b594655a62c609a7e354ecfe5752e35f,
research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py,
Gitblob edec614abba57800e220c3580549014335f0d1c4,
SHA256850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884.
Its complete authenticated body was read. Neither the general forest algebra
nor its death polynomials are claimed as new. The new pure coefficient receiver
reuses its death_polynomial and tree representation, without a graph engine,
forest enumerator or physical simulator.

The HAND claim is the following explicit specialization of the ACTUAL source
program. Given an existing original N,C,r, a literal NonrootBigon B, and an
actual source-valid input s whose CURRENT live roots are at B.parents.hybrid,
bigonCurrentKernel has the full labelled forest probabilities below on the
carrier R=SelectedCopy(state s).live. Its original opaque trees are grafted
afterward by the existing actual_current_roots_complete_graft_law. No original
descendant-count cap is imposed. No desired kernel equality is an input.

Write delta=age(B.upper)-age(B.parents.hybrid)>0 and

    x=exp(-r.edge(parent0)*delta),
    y=exp(-r.edge(parent1)*delta), p=1-native_gamma.

Thus p is P(original parent0). The physical two arms share the SAME delta.
The conclusion concerns literal pulse/interval/parent0-exit/parent1-exit.
It does not identify an arbitrary calendar segment with that local program.

## Full ordinary row, for every m

Let F be a rooted binary unranked labelled forest partitioning the m distinct
CURRENT-root tokens, with k components. For each internal vertex v, let s(v)
be the number of token leaves below v, and put

    H(F)=(m-k)! / product_internal_v (s(v)-1),
    lambda_j=j(j-1)/2,
    W(F)=H(F) / product_(j=k+1..m) lambda_j.

H counts all possible time orderings of the specified labelled merger events.
Indeed an internal event follows its descendants; interleaving the two child
event orders proves the tree hook formula by induction. Interleaving component
orders gives the displayed forest formula. Each particular merger history has
embedded-chain weight product_(j=k+1..m)1/lambda_j: unordered pairs are uniform
at each root count. Waiting times depend only on that count, so this history
choice is independent of the pure-death waiting times.

For m>=k>=1 define the rational polynomial

    D_mk(z) = [product_(j=k+1..m) lambda_j]
              * sum_(j=k..m) z^lambda_j
                   / product_(l=k..m,l!=j)(lambda_l-lambda_j).

The rates lambda_1,...,lambda_m are distinct. Partial fractions of the finite
pure-death resolvent, or its triangular forward equations, give this formula
for P(m roots -> k roots) at pair survival z. Therefore the ENTIRE labelled
ordinary row is

    E_m(z)[F] = W(F)*D_mk(z).                         (1)

For m=k=0 take the empty-forest probability1. Invalid leaf sets or nonbinary
forests have probability0. The formula has no per-m fitting or interpolation.
It is exactly the retained death_polynomial times embedded_merger_law weight.

## Full independent bigon row, for every m

For A a subset of the COMPONENT TREES of output F, let F_A be that subforest
and n_A its token-leaf count. Then

    B_I(x,y,p)[F] = sum_(A subset components(F))
       p^n_A*(1-p)^(m-n_A)
       * E_(n_A)(x)[F_A] * E_(m-n_A)(y)[F_complement_A].       (2)

The component leaves are precisely the initial roots routed to that arm.
Cross-arm mergers cannot occur in the arm interval, so every output component
lies wholly in one arm. Conversely its component assignment determines one
initial token routing, with exactly the displayed CURRENT-root coin weight.
The two within-arm processes then give the two ordinary full forest rows.
This partitions every output event once. It retains every rooted labelled
forest, not only its no-merger probability or a marginal quartet.

Importantly n_A counts input CURRENT-root tokens. It does not count output
components, original sampled descendants inside opaque trees, or individuals
after a merger. The sum has 2^k terms, rather than 2^m initial routing cases.

## Actual original-source derivation of (1),(2)

All following original bodies were read at Commons1138a5b1a281caa00b38e0976db95b586938754b,
under research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/<SHA>.lean:

- SourceForestIntrinsicGenerator, b282351bf116ae756c7e9c6ee1e3cbace41a8d753b47cac7e53c4a918c82d16f.
- SourceStepGeneratorBinding, 8021b8bddcc5cd070185843ca5454dfb289572a2592854efbbdd9e41d48396d0.
- G1UnrankedActualGenerator, 70f7f49954c09f54d37594ada58a98364c95d1bfc088c5a4e00f68ea8071f909.
- G1UnrankedNaturalPulse, 71e606368e4b0c4a8933ca9e2f067588afc064b4fa731ea74e88c32e6dbb28d2.
- G1NonrootBigonKernel, 7e228b06208880369b455914a855249337b6acecf9b4c9d70067c7ff9baab003.
- G1OriginalCurrentRootReconstruction, d5331d24f331235712f10cf66d25a8c5062a376d86249dd2def9d5497c399956.

1. actualCurrentRootCode initializes the smaller carrier R with singleton
   token genealogies, all at the input node, retaining the SAME original
   register. This initialization is constructed from s, not postulated.

2. actual_source_unranked_private_boundary_measure derives the product coin
   measure on actual current blocks. Here those blocks are singleton tokens.
   Its true/false parent convention gives the weight in (2). The actual common
   boundary instead routes every token by the entering ORIGINAL stored bit.

3. actual_bigon_pulse_on_arms places every token in its selected original arm.
   actual_time_copy_population preserves each token's arm throughout the
   actual source time kernel. Thus a fixed routed token set A cannot change
   during the interval. Source validity makes its two full unranked forest
   views well-defined and disjoint. Every other original population is empty
   on this smaller carrier. This is a reachable-state fact derived after the
   literal pulse, not an assertion about every full-Code state in N.

4. The literal viewPopulationGenerator is rate/2 times the sum over ordered
   distinct current-block pairs. Source validity gives one current owner per
   block. The two orders produce the same unranked graft, so each UNORDERED
   forest pair has exactly its original arm rate. This identifies the whole
   generator on the two-arm forest view: Q=r0*Q_A+r1*Q_Ac. Q_A acts only in
   A and Q_Ac only in its complement, so they commute on the fixed product
   carrier. No scalar diagonal identity is substituted for a full generator.

5. sourceStep_selected_expectation_intrinsic binds the actual normalized step
   to I+Q/R0, with R0 the ACTUAL proved globalRateBound of the smaller source
   carrier. Keep that same R0 on both sides. Mapping the actual Poisson series
   gives exp(delta*Q); the identity follows by the finite matrix power series.
   Commutation gives exp(delta*r0*Q_A) exp(delta*r1*Q_Ac). This derives the
   two-arm product in (2) from actual rates; no independence law is assumed.
   A larger unused global clock cancels in this Poisson identity. Full and
   smaller source clocks are not asserted equal.

6. actual_bigon_program_kernel expands the literal program with BOTH actual
   original exits. They change populations, not the unranked genealogies.
   actual_bigon_two_exits and actual_nonroot_bigon_exit_population put the
   result at B.upper. The output forest is exactly the union of the two arm
   forests, giving (2). One occupied arm gives (1) for the conditional COMMON
   bit. The retained original root/ancestral completion is not silently added.

7. actual_current_roots_complete_graft_law and the contextual replacement
   theorem restore every opaque entering original subtree, history and SAME
   register. Their actual joint-case theorem integrates that original prior
   once. The new finite coefficient formula supplies the numerical row at
   this use site. Formalizing the product-forest decoder, reachable support,
   unordered-pair map and Poisson calculation above remains an explicit Lean
   obligation. The existing source bodies and the HAND derivation are not
   evidence that this new complete adapter compiled.

## COMMON, finite words and the degree bound

For fixed entering bit false the complete COMMON row is E_m(x); for true it
is E_m(y). Under the actual original unused-bit prior alone it averages to

    B_C(x,y,p)=p*E_m(x)+(1-p)*E_m(y).                 (3)

A prefix/exterior that reads that bit must retain its correlated entering
case. (3) cannot be inserted as an independent resampling rule at each cell.
For a whole original word, fix the complete original bank, compose the rows
with that SAME bank, and integrate its actual prior once. Independent pulses
still use their own actual current-owner coins. Paired channels retain the
same x,y,p and actual protocol; separate row averages do not authorize a new
joint tensor law.

On any forest input, label its CURRENT component roots, apply (1),(2) or the
fixed-bit row, and graft their opaque trees. Every piece returns to its typed
upper node. Induction using actual_original_local_word_composition therefore
gives the entire full-forest row for EVERY finite literal OriginalSpan. No
new rank or cap needs a separate recurrence. The inherited forest algebra's
graft convolution is the same finite operation.

For initial cap m, ordinary survival degree is at most lambda_m. In (2),
ex+ey<=lambda_(n_A)+lambda_(m-n_A)<=lambda_m and coin degree<=m. A following
ordinary connector contributes at most lambda_m. Hence a full cell has total
degree at most 2*lambda_m+m=m^2 in its own four survival/coin variables. A lead
and N cells have total degree at most lambda_m+N*m^2. Every supplied finite
word has a finite exact polynomial evaluation. This bound depends on N and
does not supply a bound on an UNKNOWN realizing word.

## Actual symbolic verification and the remaining original gates

New pure source g3_all_cap_forest_coefficients.py SHA256
958061170e97f9bde60f114086c6d9c1df7f4ebe746f88ceabfe0a3525a8990d.
It computes H(F) by iterative postorder, then evaluates (1)--(3) symbolically
using the authenticated retained death polynomial. It creates no new model.

verify_g3_all_cap_forest_coefficients.py actually PASSED:

- ALL2745 ordinary forest coefficients for token counts0 through6 match the
  retained complete embedded-history enumeration and ordinary polynomials.
- ALL628 bigon coefficients, both modes and every complete labelled forest
  through cap5, match the retained full cell polynomials with formal connector
  variable evaluated at1. This identity comparison creates no nonstrict
  physical source or positive-epsilon tuple.
- Four malformed-input refusals and a1100-token deep caterpillar hook count
  pass. The latter tests iterative depth handling, not a full cap1100 row.

Complete symbolic rows, source bodies/hashes and failures-if-any were encrypted
before persistence with the existing identity:

    [encrypted runtime receipt retained privately]
    ciphertext c4702abf59975fbeba30c8b2bd063e7ff7c79c610d68c9b802fb708c90c521e4.

These are finite controls of a uniform HAND argument, not verification at
every cap or a kernel/axiom audit. The actual new Original-Code/canonical
decoder is UNCOMPILED. No complete original graph was executed or refitted.

Fresh N'/Code BinaryValid/RegistryValid, protected old IDs/menu/calendar/rates,
Originated, the exact selected local word inside a concurrent larger calendar,
actual exterior/readout/finish binding and arbitrary joint observation fibres
remain explicit. This result neither proves an arbitrary large-cap return
family nor adopts any G4 candidate. The all-input one-witness bound H(p), or
an equally complete NO mechanism, is still missing. The octic exact-zero
gate is still open. Forward formulas for arbitrary m,N do not decide inverse
existence over all N.
