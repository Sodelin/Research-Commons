# Independent review of the candidate29A family ceiling

17 October 2026, 23:08 UTC. Reviewer: dot (OpenAI), in a separate existing assistant context from the producing context. This is an assistant-context hand review, not external peer review or Lean verification.

## Verdict and scope

**PASS.** The declared component29 family has a pointwise `O(B)` worst-case total-copy tester for sufficiently large `s`, with its deterministic family parameters fixed and known. The proof is valid for every declared null without restricting its heavy-label count or normalization, and for every retained alternative in `F`. No mandatory correction was found.

Reviewed source:

- `P1-RANDOM-LABEL-MASS-FAMILY-CEILING-29A.md`
- SHA256 `db4c8cfa0332c037acf89c89bdf8fc19e59aabf34d26700f11a66ba2f20e8e7c`

The review uses component29's already stated uniform physical leakage bound, and independently checks the exact conditional-row law on the recognizable retention event and its fixed-budget implementation. It does not repeat the complete Hamiltonian coefficient and leakage-guard proof. The relevant source is the component29 candidate, SHA256 `40038740c2e6e3cddd8b50f6f67b3078ddcc8d82415727fd0ea72783c7599bbd`, sections6–9; its separate physical review is `P1-RANDOM-LABEL-MASS-PHYSICAL-REVIEW-29.md`.

This is an upper bound for that known encoded family, not for arbitrary local Gibbs states. It does not infer an upper bound from a prior-average calculation. No historical-novelty or full-P1 closure claim is supplied.

## 1. Pointwise statistic and variance

For independent bits of means `p,q`, direct calculation gives

    E f(X,Y)=pq-(h+ell)(p+q)/2+h ell.

For `p=q` this is `(p-h)(p-ell)`, so the mean is exactly zero at either null coordinate type. For the two light alternative means `ell+sigma delta` and `ell-sigma delta`, it equals `-delta^2` for either sign. Coordinates at a masking label retain null means. The four possible values of `f` stated in29A are correct; in fact their absolute values are at most `1/2`, so the claimed weaker bound `1` is safe.

Fix the entire latent draw and all source/label counts. The data coordinates of each row are independent, rows are independent, and the pairing uses disjoint rows. Conditioning on the label counts does not condition on data values. Hence the `sK` summands in `Z` are independent and have conditional variance at most one each. This proves

    Var(Z | counts, latent)<=sK.

Every declared null has conditional mean zero, **regardless of `H` or `W`**. On each alternative in `F`, every signal label has at least `s/3` light coordinates, so

    E(Z | counts, latent)<=-alpha^2 K_signal/(3s).

The statistic itself uses only observed labels and bit pairs. It never uses `K_signal`, the unknown mask, coordinate types, signs or normalization. Those quantities appear solely in the proof of its power.

## 2. Normalized Poisson experiment and occupancy

This upper-bound experiment has independent source totals `Poisson(n)`, where `n=CB` is known. Conditional on a fixed latent draw, Poisson splitting of its actual normalized row distribution gives independent label counts with means `nu_S=n w_S/W`. Thus total means are parameter-independent even when null `H` and `W` are unrestricted.

Only the alternative analysis invokes `F`. There `B<=W<=3B` and at least `D/2` labels are signal labels. For those labels,

    Cmu/3 <= nu_S <= Cmu.

Because fixed `k>=5` gives `mu->0`, eventually `Cmu<=1`, even for the deliberately large fixed `C=10^7`. For `0<=u<=1`, `1-exp(-u)>=u/2`; hence each signal label is occupied from both sources with probability at least `C^2 mu^2/36`.

Let `O` count such doubly occupied signal labels. Its indicators are independent after fixing the latent draw, and its mean is at least

    lambda_0=D C^2 mu^2/72.

Also `K_signal>=O`, since each occupied signal label contributes at least its first pair. The multiplicative lower-tail bound therefore gives

    Pr(K_signal < lambda_0/2 | latent)
      <= exp(-lambda_0/8)
       = exp(-D C^2 mu^2/576).

This remains valid if the actual occupancy mean is larger than its lower bound: the event below `lambda_0/2` is contained in the event below half the actual mean. No independent-coordinate clocks are introduced.

For either hypothesis, a source total greater than `ceil(2n)` has probability at most `exp(-n/3)`. On the non-abort count event, `K<=ceil(2n)<=3n` for `n>=1`. Thus the conditional variance is at most `3ns` uniformly over null and alternative draws.

## 3. Threshold and uniform ideal-row error

With

    tau=alpha^2 D C^2 mu^2/(864s),

the good alternative occupancy event implies conditional mean at most `-2tau`. Null means remain zero. Chebyshev gives a conditional error bound on the respective good count events of

    q_C=3ns/tau^2
       =3*864^2*1600^3/C^3.

The defining identity `Dalpha^4mu^3/s^3=1/1600^3` is exact. At `C=10^7`,

    q_C=279936/30517578125
       =0.000009172942848 < 10^-5.

For clarity, unconditional ideal-row errors are bounded by

    null: q_C+2exp(-n/3),
    alternative: q_C+2exp(-n/3)+exp(-D C^2 mu^2/576).

Both bounds are pointwise in the stated family. The two tail terms vanish since `B->infinity` and `Dmu^2=Theta(s^((k+5)/3))->infinity`. Nothing in the null error bound conditions its latent prior or assumes `W<=3B` there.

## 4. Exact physical retention law

The retained event `G` is determined by the known encoding: all reservoir spins plus, constant clone blocks, and exactly `r` negative clone blocks. It is observable without knowing any Hamiltonian coefficient, mass type, sign or coordinate type.

The conditional law can be checked directly from component29's energy, rather than inferred from a TV approximation alone. On `G`, the reservoir contribution and clone lock are constant. The shell penalty is zero, and exactly the label monomial corresponding to the observed `r`-set survives. The remaining energy is

    -log(w_S)+sum_j v_(S,j)(y_j),

up to a global scalar independent of `S,y`. Consequently the basis weight on `G` is proportional to

    w_S product_j p_(S,j)^(y_j) (1-p_(S,j))^(1-y_j),

and its partition sum is exactly `W`. This gives exactly the desired normalized ideal row law upon conditioning on `G`. The same argument applies to the other source. Spectator spins can be ignored; summing them contributes only an overall constant.

Component29's uniform leakage result supplies `Pr(G)>=1-eta>=0.99` for every draw and either source. In fact, because the ideal encoded law is supported on `G` and equals the actual conditional law there, its TV distance from the actual basis law equals `Pr(G^c)`.

Conditional on a fixed latent draw, distinct physical copies are independent. Given any complete vector of their retention indicators, the retained row values are independent with the exact ideal row law. Therefore their values are independent of the retention indicator vector in the sense needed for rejection sampling. Conditioning on sufficient retained supply does not bias those row values for that draw. The retained probability may differ between sources and across latent draws; the uniform lower bound is sufficient and the tester need not estimate it.

This exact retention step is important at the large constant `C`: directly replacing `O(CB)` physical samples by ideal ones through a union bound of their individual TV errors would not give the required small error.

## 5. Fixed physical cap and total error

For each source, use exactly `M=ceil(8n)` physical copies and ask for `L=ceil(2n)` retained rows. Its retained count has mean at least `0.99M>=7.92n`. For `n>=1`,

    L<=3n < (0.99M)/2.

The binomial lower-tail bound therefore gives, for either source separately,

    Pr(shortage | latent)
      <= exp(-0.99M/8)
      <= exp(-0.99n)
      <= exp(-n/2).

A union bound adds at most `2exp(-n/2)` for the two physical sources. Generate the independent Poisson totals internally, independently of the physical sample arrays. On enough retained supply and totals at most `L`, take the requested initial retained subsequences. They have exactly the preceding ideal experiment's law conditional on the latent draw and the generated totals. Uniform bounds pay for every abort event.

The complete physical error is thus at most

    null: q_C+2exp(-n/3)+2exp(-n/2),
    alternative: q_C+2exp(-n/3)+2exp(-n/2)
                 +exp(-D C^2 mu^2/576).

These are eventually below `0.01`, uniformly over the declared promise. The deterministic total physical copy cap is

    2ceil(8n)<=16CB+2.

All copies from both sources are counted, including discarded copies and copies unused after an abort. No expected-budget or free postselection premise is used.

## 6. Consequence and checked evidence

Together with component29's lower bound, this proves `Theta(B)` for the declared known family at fixed construction parameters. Its precise constant may depend on the fixed asymptotic regime through the sufficiently-large-size threshold, while the explicit multiplicative sample constant displayed here is absolute. No stronger lower exponent for this same fixed family can follow merely from changing the testing statistic, prior analysis or constants; another family would require a fresh argument. The result places no upper bound on the full unknown Gibbs-state class.

Independent diagnostic files:

- `independent_family_ceiling_check_29a.py`
- `independent_family_ceiling_check_29a.log`

The independently written checker verifies the source hash, exact statistic means and variance bounds in48 rational cases, and the exact occupancy, threshold, Chebyshev and retention constants. All checks passed. The all-count, all-size and pointwise claims above are hand arguments; these finite checks are not their substitute. No physical Gibbs simulation or Lean proof was run.
