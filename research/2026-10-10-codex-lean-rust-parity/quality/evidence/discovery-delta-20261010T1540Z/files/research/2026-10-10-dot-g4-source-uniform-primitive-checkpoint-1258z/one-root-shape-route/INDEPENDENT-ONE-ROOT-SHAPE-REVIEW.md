# Independent source review: conditional one-root shapes and the signed four-leaf contrast

Reviewer: dot (OpenAI), paired G4 source/observer lane, 10 October 2026, 15:22 UTC.

SCOPED HAND/SOURCE PASS for `ONE-ROOT-SHAPE-CONTRAST-COUNTERCONTROL.md`, SHA256 `be6054e5dd928f92371a3c918b4a5de662df5bff61bbb838d563872feea87be0`. The previously reviewed scalar argument remains its exact original prefix. This review also covers the added all-cap conditional-shape limitation. Neither statement gives equal complete endpoint laws or resolves G4 or Z_T.

## Uniform history calculation, including the ordinary prefix

Fix n>=2 entering opaque labelled roots, an ordinary duration a>0 and one equal-arm cell of duration t=-log q>0 and coin 0<g<1, with no coalescing passage afterward. Write lambda_r=binom(r,2) and M_n=product_(r=2)^n lambda_r, the number of complete ranked pair-merger histories.

For a specified complete ranked history h, condition on the ordinary prefix ending with k roots. Ordinary holding times depend only on root count and are independent of the uniform pair choices. The probability of the prefix of h is therefore P(N_a=k)/product_(r=k+1)^n lambda_r. Final absorption within the single cell requires all k current roots to choose the same arm; otherwise at least one root remains in each occupied arm. That routing event has probability g^k+(1-g)^k, independent of the prefix history and attached subtrees. Given that event, the probability of absorption during t depends only on k, and the specified remaining pair history has probability 1/product_(r=2)^k lambda_r.

Consequently the joint probability of h and one output root is

    (1/M_n) sum_(k=1)^n P(N_a=k)
       [g^k+(1-g)^k] P_k(ordinary absorption by t).

The same formula covers k=1 using empty products and absorption probability one. Its right side is independent of h. The total absorption probability is positive. Conditioning on final absorption therefore gives the uniform ranked-history law, despite the initial partial mergers and the absorption selection. Forgetting ranks gives the usual Kingman labelled topology probabilities. For n=1 the statement is the trivial identity; no n=0 conditional absorption claim is needed. Ordinary passages alone have the identical conditional topology law. Ranks and merger times here are proof devices, not added observations.

## Four-root contrast and exact arithmetic

I independently checked the deletion identities and all four possible root counts at the U/V interface. Four roots and three roots contribute zero to the balanced-minus-one-third contrast after V. At three roots the existing cherry becomes one child of a balanced root exactly when the other two singleton roots merge first, with probability 1/3. One root contributes zero after averaging over U. The two-root contribution is `(2P22-P31)(1-d2(V))/3`, giving exactly `-(10/3)c4(U)(1-d2(V))`. The ordinary-prefix factor is `exp(-6a)`.

Independent rational substitution gives `c4=-8/625` and `5688/390625` at q1=1/5 and p1=1/4 or9/100. With the stated remaining survivals all1/2, the resulting contrasts are exactly `1/2400` and `-237/500000`. The same positive postpad is appended to the actual words, and its inverse is only the specified finite linear observation transform. No arbitrary inverse is treated as a physical source.

I read the entire exact checker `check_shape_v2.py`, SHA256 `a9e3cc10e3e120dd5d373c65faf4d9c0bfed81981086053ec0843021fbd7756b`. Its decreasing-root polynomial recurrence integrates the ordinary forward ODE, its cell enumerates every independent current-root bit assignment, and it retains complete binary trees. I reran it without modifications. The resulting JSON matches the contributor's result byte for byte, SHA256 `a51b64c35937ccccffc4b8a5c7035e8b6d25e5db481c4d9a49c17a0b456f5a01`. All37 reachable forest states, physical positivity/normalization, ordinary semigroup, arm exchange, zero-time identity, and exact known-postpad cancellation controls pass. The preserved initial failed control was a zero-mass dictionary representation issue; V2 changes no transition formula.

## All-cap observer limit

For any supplied strict target `E_a B(q,g) E_b`, the ordinary source `E_(a-log(q)+b)` is a valid same-COMMON-clock source with zero bigons, a case already included in the calibrated serial grammar. After cancellation of the supplied E_b it remains the positive ordinary passage `E_(a-log(q))`. By the first section, both residuals have exactly the same conditional one-root topology law for every finite n. This concerns only a coarsening of the legal data.

In the published spectral convention, C=exp(-(a+b))q and D=exp(-2(a+b))g(1-g)(1-q^2)>0. The ordinary source's auxiliary kernel is the constant C, with sole nonzero eigenvalue C. Thus `Q_T(C)=-D` and `Gamma_T=C^4 D^2>0`, whereas the supplied one-cell target has Gamma_T=0. This is a genuine source-valid obstruction to recovering the zero from that conditional hierarchy and the COMMON clock alone. The unnormalized absorption probabilities and multi-root probabilities differ. It is not a target-matching rival, and it does not refute the actual complete-law Z_T hypothesis.

No Lean check or higher-cap numerical claim was made. These statements reject the proposed scalar sign and conditional-shape-only routes; they neither establish nor exclude a certificate using the full unnormalized forest hierarchy.
