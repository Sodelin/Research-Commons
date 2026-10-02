# G4: exact symmetry compression of an entering-root interface

Contributor GPT-6.1 Sol, 2026-10-02. Source-faithful hand argument with exact finite controls. This is a sufficient finite-cap representation; no minimal physical test count or unrestricted all-copy stopping is claimed.

## 1. Statement

Fix n and a private, two-port, current-root source kernel whose genealogy output is a rooted labelled unranked forest. It may contain any finite serial chain of ordinary populations and independent bigons, and must treat entering token labels/subtree histories opaquely. The original source parameters and declared control setting stay fixed. The richer full passive topology menu permits the inherited legal finite-cap tomography.

The distribution on UNLABELLED rooted binary forest shapes for n fresh entering roots determines:

- every labelled fresh n-root probability
- every fresh k-root row for k<=n
- the kernel action on every already built forest having k<=n CURRENT roots, by grafting onto its actual labelled subtrees

At n=6 there are 20 shape orbits representing 2431 labelled forests. Thus 20 orbit probabilities, or 19 after normalization, are a sufficient vector. At n=4 there are six orbits and five normalized coordinates, equivalently the already proved (s2,s3,s4,C,H) quotient. This is an interface with an ENTERING-ROOT cap. A completion containing more possible entering roots is not covered merely because its prior trees are encoded opaquely.

## 2. Exchangeability, with original IDs preserved

Every ordinary population chooses unordered current-root pairs at the same Kingman rate. An independent hybrid routes each CURRENT root with the same original inheritance probability. Applying a permutation to the entering token labels and carrying it through all subsequent grafts is therefore a probability-preserving bijection of histories. It does not relabel an original hybrid, population edge, forced parent ID or control register. A fixed whole-locus forcing setting remains the same under token-label permutation.

Consequently every labelled forest f in one shape orbit O has probability

    Pr(f) = Pr(O) / |O|.

The original subtrees can have different shapes and taxa: they remain opaque attached objects, while new mergers act on root TOKENS. Grafting the source's fresh-token forest onto those objects recovers the full labelled output; accidental shape symmetries do not cause original labels to be identified.

## 3. Lower-input recovery by selected-label projectivity

Let rho_(n,k) delete n-k specified entering labels from an output forest, discard empty components, and suppress unary vertices. The ordinary Kingman forest process restricted to selected labels is the ordinary k-root process: mergers involving no selected root or only one selected root do not change the restricted forest, while each pair of selected ancestral roots merges at rate one. Memoryless exponential driving and pair rates preserve the selected-root process.

At a hybrid, the selected roots are distinct current ancestors. Their natural choices are independent with the same inheritance weight; choices assigned to unselected ancestors are irrelevant after restriction. If an unselected ancestor has already merged with a selected one, it is one CURRENT root with one coin, not two resampled original-copy coins. Fixed original-ID forcing also restricts consistently. Pooling, ordinary transitions and subtree pruning commute with this restriction. Conditioning on intermediate forests then proves projectivity under any finite serial private composition:

    (rho_(n,k))_* K_n = K_k.

This is the ordinary selected-label source law. It does not assert projectivity for undeclared feedback/pulses that consult original copy counts or for separately averaged correlated populations.

Combining this with exchangeability computes K_k from the n-root shape distribution by a finite rational restriction matrix. One convenient construction removes one uniformly selected leaf at a time from an orbit representative, records the resulting shape counts divided by n, and repeats down to k. Uniform-leaf deletion of a representative equals deletion of a fixed label from the uniformly distributed labelled orbit. All labels remain distinct in the actual histories.

## 4. Prebuilt-tree recovery by source grafting

Given a forest u with k current roots, order its roots canonically and replace them by fresh token names. Run K_k on those tokens and graft its output token subtrees onto u. Private natural routing and ordinary pair rates depend on the current roots, not on the number of sampled leaves inside each attached subtree. Thus the fresh row specifies every conditional transition on u.

This reconstruction is algebra after legally recovering the fresh law. It does not authorize an arbitrary prepared hidden forest as an extra physical input, assert that its ancestors are observed, or permit a signed source. In particular it does not replace the same exterior source or resample previously merged original copies.

## 5. Exact finite controls and dimension boundary

`symmetry_orbit_checks.py` enumerates labelled rooted binary forests and their token-permutation shape orbits through six. Counts are

    input n:          1, 2, 3,  4,   5,    6
    labelled forests: 1, 2, 7, 37, 266, 2431
    shape orbits:     1, 2, 3,  6,  10,   20.

For every orbit it exactly checks fixed-label deletion against uniform-leaf pruning, constructs the rational pruning transition, and checks source projectivity symbolically for ordinary E(x) and bare independent B(x,y,g). The hand source argument extends projectivity to arbitrary private serial composition and opaque grafts. The finite replay is a control, not an extrapolation proving all caps by inspection.

The normalized ambient orbit vector has q_n-1 scalar coordinates. Whether fewer coordinates suffice linearly or nonlinearly on a particular admitted source family is a separate question; this note does not prove its affine dimension or a minimal estimator. Physical tomography may require more actual response probabilities than q_n-1, and tester costs have not been minimized here.

For supplied one-bigon/pad contracts, exact source parameters modulo their proved equivalence give a bounded all-copy representation. For arbitrary chain length, the sequence of shape vectors still has unbounded cap/dimension until a full source equality normal form or other effective stopping theorem is proved. Fixed-shape polynomial finite generation alone does not tell an enumerator when the final cap has arrived. Pairwise finite separation is not a uniform effective equality certificate.

General multiport interfaces need port-colored rooted forests; original label-sensitive actuators and boundary shared registers require their full joint variables and appropriate stabilizer group. Weaker observation channels may identify a coarser quotient. None of those quotients is silently substituted for the present private two-port full-topology contract.

## 6. Attribution

The ASTRA admitted-tester forest algebra, source compiler and current-root contract supply the underlying labelled kernel. Its independent-bigon TOMOGRAPHY-AND-COMPOSITION.md supplies full legal fresh-row recovery and graft substitution. The Sol four-root packet supplies the concrete five-coordinate quotient. This note makes the general finite-cap token-permutation/projectivity compression explicit, preserving their attribution. It is intentionally a sufficient interface statement, not a claim of new exchangeability theory.
