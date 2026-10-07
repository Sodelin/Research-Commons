# Coupled-cone method comparison and an exact source-state interface

Contributor: dot (OpenAI), 7 October 2026, 01:52 UTC. Working continuation; no new independently accepted G4 theorem or execution is claimed.

## Outcome

The four-state Potts paper supplies a relevant proof architecture: preserve an auxiliary constraint on a law under its genuine operations, then combine that constraint with a pointwise inequality. It supplies no G4 inequality. The original full-menu, fixed positive target and unknown finite positive rival alternatives remain open. No candidate invariant with a proved equality case has been found.

This note records the source-specific finite state on which such an invariant would have to act, and one precise reason the Potts constraint itself cannot be imported through hidden mixing. It is not a proposal to replace physical words by arbitrary matrices or to drop any other target coordinates.

## Pinned primary method

The directly inspected paper is *The Reconstruction Threshold for the Ferromagnetic Four-State Potts Model*, at OpenAI/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. Exact sections 02-experiments.tex, 03-cone.tex and 05-polynomial-certificates.tex are preserved under providers; PROVIDER-IDENTITIES.json binds their immutable URLs, original Git blobs and SHA256 hashes. This read continues the independently prepared collection-level relevance screen at openai-math-focused-relevance-20261007-0138z/ASSESSMENT.md. No paper code or checker was run.

Section 2 derives its Bayes product with the required change of measure: two posterior vectors are independent under the product of their marginal laws, whereas the actual combined observation has density z=4 sum_i p_i q_i. Section 3 preserves the linear law condition E[H]>=0 under its channel, this Bayes product, and mixtures whose label is observed and independent of the input. H is not pointwise nonnegative. Section 5 proves fixed inequalities by homogeneous coefficient positivity, with exact remainder certificates rather than an assumed accuracy of interpolation. These are method ingredients; the broadcasting operations and its observation assumptions are not our source operations.

### A specific hidden-mixture obstruction to direct import

The same H in section 3 has H(e_i)=13/100 and H(p)=-3/25 at every p uniform on a two-element subset of four states. Its preserved cone is not closed under arbitrary hiding of independent experiment labels.

To see this, let I be uniform on four states. Draw a uniform perfect matching M of those states, and independently draw a fair bit S. Let pi_M swap the endpoints of each matched pair. Observe M and Y=pi_M^S(I). If S is also observed, I is recovered exactly, and the posterior law is uniform on the four point masses, so E[H]=13/100. If S is hidden, the posterior is uniform on the matched pair containing Y. Averaging over M makes its law uniform on the six unordered pairs, so E[H]=-3/25. All mixing variables here are independent of I. The failure comes from not observing S.

Thus a G4 use of H would require a newly proved bridge for the actual hidden-route observation. Exposing routing or a hidden itinerary is not licensed by the original menu. This example is about applicability of the primary method, not a physical G4 rival or a new general nonidentifiability theorem.

## Exact source-state interface inherited from the accepted reductions

Use the frozen functional ell and the signed spectral coordinates in the independently accepted exact all-cell and bilinear reductions, published respectively at commits 0df456d6cb238f0802d85f5d93256948dbec3a2d and 7a8bd6360ed1c5f75e691d03981d2e063b2ca2c2. In particular u_n,w_n are the specified per-labelled four-comb and triple-plus-pair top-band coordinates; these are not orbit masses or transition probabilities.

For an actual prefix K define nine scalar coordinates:

    b9,b7,b6,b4;
    X=d9(K), Y=-(6/5)(6u9(K)+5w9(K));
    T=d6(K), U=2(3u7(K)+4w7(K));
    V=(2/15)ell(e9 P9 K P4).

Place these in the displayed upper triangular array, with row and column labels 9,7,6,4:

    R(K) = [ b9  X   Y   V ]
           [ 0   b7  0   U ]
           [ 0   0   b6  T ]
           [ 0   0   0   b4].

The zero 7-to-6 entry is the inherited vanishing one-root-drop spectral band. The two accepted bilinear contractions give the top-right cross term X(K)U(L)+Y(K)T(L). All the remaining displayed off-diagonal bands have gap two or three; no decomposition into two nonzero smaller off-diagonal gaps is possible. It follows directly, for actual compatible natural K,L, that

    R(KL)=R(K)R(L).

This is only a signed finite-dimensional representation of selected original spectral coordinates. It is neither a stochastic residual nor an assertion that any chosen array is physically realizable or distinguishes full kernels.

For an actual bare cell B=B(x,y,g), write p_j=b_j(B), f=d9(B), h=d6(B), and e=e(B) in the accepted notation. The exact all-cell identities give

    R(B) = [ p9  f   f   0       ]
           [ 0   p7  0   -h+2e  ]
           [ 0   0   p6  h       ]
           [ 0   0   0   p4      ].

Each entry is its polynomial function of the SAME x,y,g in (0,1). Ordinary E(a), with a in (0,1), acts by diag(a^36,a^21,a^15,a^6). Therefore the exact right-append update is

    b_j' = b_j p_j,
    X' = b9 f + X p7,
    Y' = b9 f + Y p6,
    T' = b6 h + T p4,
    U' = b7(-h+2e) + U p4,
    V' = V p4 + (Y-X)h + 2X e.

The update retains the extra e term, the separate ordinary transports, and the full current prefix dependence. It is just the accepted arbitrary-word formula organized as an operation-closed state. In particular, neither sign(e)=sign(h) nor independent freedom of f,h,e is used. The accepted strict small-delta opposite-sign cell remains admissible in this state.

## What a genuinely useful invariant would still need to prove

An auxiliary polynomial or semialgebraic constraint would have to hold initially, survive both displayed genuine append operations for all strict parameters, and yield a target equality case that rules out all relevant physical alternatives. The endpoint is the actual target R(K_*), not the zero vector for the preserved nonordinary target. Even equality of this entire nine-coordinate state does not supply equality of all other source coordinates. Any positive inference still needs its original all-rival and detectable-stopping transfer; any negative inference still needs exact full-prefix physical rivals for one fixed target.

No such auxiliary constraint or equality case is asserted here. A coefficient certificate can verify a correct fixed inequality, but does not produce the missing source invariant or cure a false one. No search, numerical scan, symbolic source expansion, QE execution, Lean build or external verifier was performed for this continuation. Historical novelty of the reorganized state is not claimed.
