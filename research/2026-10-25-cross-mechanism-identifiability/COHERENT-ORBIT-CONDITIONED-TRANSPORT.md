# Coherent orbit-conditioned transport of actual joint response kernels

Author: dot (OpenAI), 25 October 2026. Written supplier candidate for coordinating review. It uses the known-entry multistar preparation and local migration identification; it does not classify an unknown next boundary or a whole unknown history. No formal verification, historical novelty or finite-data stability is claimed.

## 1. What must be transported

GLOBAL-CUT-TRANSPORT-GATE.md proves that survivors at an arbitrary internal cut need not have product hidden locations. We therefore transport the complete n-lineage response vector, not an assumed new independent-entry law.

Suppose the multistar construction has identified the entry parameter multiset and a migration-generator orbit in one declared constant epoch. Fix n main blocks. Extract a single population-partition component with K blocks in every hidden deme, where K is large enough for all main blocks and the disjoint migration probes below. The entry pairs (p,lambda) mark visible classes. The actual response is one uniform mixture over the finite group G of hidden assignments preserving those marks. The same mixture is used for every test and every selection of main blocks.

Let z_sigma be the off-diagonal migration vector in the visible-class coordinate system under sigma in G. Its finite orbit support Z and its positive weights have been recovered by the prior local theorem. Pick one z_* in Z. This is a coordinate choice, not a physically selected hidden state.

## 2. Mixed probe/future coefficients are observable

Reserve n labelled main blocks in any desired visible-class configuration a in {1,...,d}^n. Use disjoint remaining blocks for h directed migration probes, with the same labelled triad patterns and fixed global merger-time ordering as in MULTISTAR-PARTITION-PREPARATION.md. Let F be any future genealogy-cylinder event on the main blocks, whose recorded times lie strictly after the shrinking probe interval. It may include no main coalescence up to a chosen later cut and a further event after that cut.

The joint leading coefficient of the probe-merger density and F, after dividing the known rate/time factors, is

    E_sigma [ z_sigma^beta R_(sigma,a)(F) ],

where beta is the multi-index of the h directed rate factors and R_(sigma,a)(F) is the actual main-block response under that same hidden assignment. This follows from the previously proved minimal-event expansion: all h required migrations occur on probe singleton lineages; an extra migration or competing coalescence adds an order or violates the prescribed history. Main blocks retain their initial locations in the leading term. After the shrinking interval, the Markov property and sampling consistency of the structured Kingman process allow the probe blocks to be marginalized.

The marginalization does not assert independence of finite-time probe and main genealogies. It uses the explicit joint leading coefficient and then the ordinary projectivity of the genealogy of selected lineages in this fixed source. Conditioning on the extracted population-partition component keeps the same sigma across all blocks and tests.

Thus every polynomial P of bounded degree supplies an observable linear combination

    E_sigma[P(z_sigma) R_(sigma,a)(F)].

The mixed coefficients, not merely unweighted Q moments, are the missing supplier for conditioning the future consistently.

## 3. Select one generator-orbit component without a hidden intervention

For each z_* in the recovered finite support define the interpolation polynomial

    ell_*(z)=product_(w in Z, w!=z_*)
       ((z-w) dot (z_*-w)) / ||z_*-w||^2.

It has degree at most |Z|-1 and satisfies ell_*(z_*)=1 and ell_*(w)=0 at every other orbit atom. Consequently

    E_sigma[ell_*(z_sigma)R_(sigma,a)(F)] / P(z_sigma=z_*)
      = E_sigma[R_(sigma,a)(F) | z_sigma=z_*].

The denominator is positive and already identified. Although ell_* may take negative values away from the finite orbit and the observation formula uses signed coefficients, on the actual orbit it is exactly an indicator. Hence the result is a genuine positive probability law, not conditioning on a signed event.

Use this same polynomial and same selected atom for every a and F. The remaining ambiguity is one fixed coset of H=Stab_G(z_*). After choosing a representative coordinate frame, it is a uniform H-mixture. Every h in H preserves the chosen Q and the coalescence-rate vector, but may act nontrivially on the unknown later history. This uncertainty is retained rather than silently removed.

A finite supply of disjoint probes suffices: h<=|Z|-1<=|G|-1. The conservative choice K=n+6|G| blocks per visible class supplies both the main configurations and all required probes. Different finite tests may reuse their designated roles in different marginals of one sufficiently large exact genealogy law; no physical repeated intervention is assumed.

## 4. Transport through the known constant epoch

Let t>0 lie strictly inside the declared constant epoch, with no intervening demographic boundary or sampling event. Let K_n be the killed generator on ordered n-lineage occupancy states in the selected coordinate frame. For a future event F after that cut define the column vector

    r_bar(F)[b]=E_(h in H)[actual probability of F from occupancy b at the cut,
                          under the corresponding later-history alignment h].

The mixed-probe extraction supplies, for every earlier occupancy a,

    y(t,F)[a]=E_(h in H)[probability from a of no main coalescence in (0,t),
                        then F].

Because the selected Q and lambda are identical across this residual mixture, the same known K_n governs every term. The Markov property therefore gives

    y(t,F)=exp(K_n t) r_bar(F),
    r_bar(F)=exp(-K_n t)y(t,F).

Finite matrix exponentials are invertible. This exact extraction is coherent across every F and a; no post-selection of a favourable permutation per event is allowed. Equivalently, H commutes with K_n, so the inverse preserves the residual-invariant response space.

There is no assertion that the conditional distribution of survivors is independent. The full n-lineage killed operator includes every pair hazard and migration transition. The positive source representation supplies the probabilistic meaning of the recovered vector despite potentially signed inverse-matrix entries.

## 5. Exact remaining boundary problem

This supplies response kernels at an internal cut only while its preceding generator is known and the interval is certified boundary-free. It does not locate the next non-silent boundary, determine its unknown independent routing matrix, recover new unreachable states, or align all later epochs. Completely silent boundaries remain representation ambiguity.

Nor does a residual H-averaged kernel automatically reveal each H-component of later history. Further jointly observed preparation/probe information may distinguish a later symmetry-breaking event, but a separate coherence argument is required. Unknown finite rival sizes and effective termination cannot be inferred from the current finite-group extraction alone.

The source-faithful advance is limited and concrete: the programme can transport an actually acquired full joint response mixture instead of illegally restarting the independent-entry assumption at every cut.

## 6. Evidence level and computational consequence

This packet is a written composition argument. No new execution or formal check is claimed. Earlier exact-rational multistar and probe controls remain relevant only at their bounded scopes. Matrix inversion, finite-support interpolation and Markov transport are classical; the task-specific issue is whether the needed mixed coefficients are genuinely supplied by legal observations, which sections 1–3 expose explicitly.

For finite data, exp(-K_n t), orbit interpolation and rare no-coalescence conditioning can all be ill-conditioned. This exact-law transport is not a stable estimator or a raw-DNA observation bridge. The end-to-end benchmark must measure that loss rather than treating the algebraic inversion as a practical protocol.
