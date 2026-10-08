# Sixth diagonal of the accepted cap-five source family

PRIMARY HAND/SOURCE ACCEPT of the new sixth-diagonal coefficient, its strictly negative sign for the preserved four-cell bank, and the original legal fourteen-copy separating event. This is a separate review of the sixth-root extension; the previously accepted cap-five construction is preserved.

The exact candidate is [SIXTH-DIAGONAL-SEPARATES-THE-CAP5-RETURN.md](https://github.com/Sodelin/Research-Commons/blob/53f6aa9f9527f0bd7b041d7e15df358ba2e16328/research/2026-10-08-cloud-g4-sixth-diagonal-0722z/SIXTH-DIAGONAL-SEPARATES-THE-CAP5-RETURN.md), SHA256 `b0b70cec96257a7fa26cb613dcddeb176c983f36047592180792e714a5902904`, 13,322 bytes, Git blob `9e5ae76b4b2faf93c1dca5021293366d7fc293f3`. All seven packet files, six manifest entries and twenty-eight contextual identities are authenticated in [the saved source record](g4-sixth-diagonal-source-authentication.json), SHA256 `695ed79714b05c3618a8c772ab32dda4e5e923f0d058555171e313f2085b883d`.

The exact earlier cap-five source is reviewed in [the primary eight-cell receipt](G4-EIGHT-CELL-FULL-FIVE-RETURN-HAND-REVIEW.md), immutable commit `dd087636d9bf4609a5df7e15229cfd79015bfa07`, review SHA256 `a40778ff44d5726ef3380c0b4919210b9ff1037841d1929debba116c7fe70bf9`. It constructs two actual positive four-cell half-coin words at fixed a,b, with full completed-forest product E(ab) through five roots. The new coefficient below concerns that SAME bank and its higher-arity action. The saved child attribution concerns the earlier cap-five placement/IFT argument only; it is not used as a sixth-coefficient verdict.

## Actual source coefficient

For one cell the no-merger diagonal is derived from actual fair current-root routing:

`b_n = 2^(-n) sum_k binomial(n,k) (s-h)^(choose(k,2)) (s+h)^(choose(n-k,2))`,

where s = 1 - A t and h^2 = w(t) t^3, with w(t) = w0 + O(t). This is a source diagonal under the original half-route law, rather than an independently chosen matrix parameter. The sixth difference is

`D6 = log b6 - 6 log b5 + 15 log b4 - 20 log b3 + 15 log b2`.

The terms at zero and one root vanish, so this is the full sixth forward difference. The independently checked new expansion is

`D6 = (15 A^6/16 - 45 A^3 w0/4) t^6 + O(t^7)`.

The h^4 term is essential to this conclusion because h^4 has order t^6. Its cancellation is checked explicitly rather than dropped as a higher-order contribution.

For equal arms, let S_n be a sum of n fair signs and u = -log s. The source diagonal gives log b_n(s,0) as a term linear in u with polynomial degree two in n, plus log E exp(-u S_n^2/4). Cumulants of S_n^2 have degree at most their order in n: a nonzero connected chosen-edge contribution must have even degree at every vertex, and hence at most that many vertices. For order six, simple cycles give leading coefficient 3840 n^6. The sixth difference kills every lower-degree term. Its factor 720 cancels the 6! denominator, leaving 3840/4^6 = 15/16 as the coefficient of u^6.

For the h^2 correction, write m = [n(n-2)+S_n^2]/4 and d = (n-1)S_n/2. The exact relation d^2-m = n(n-2)(S_n^2-1)/4 gives the logarithmic correction

`h^2 n(n-2)/(8 s^2) (E_u S_n^2 - 1)`.

In the tilted cumulant expansion, the terms through u^2 have degree at most five in n. At u^3, the leading fourth cumulant coefficient 48 n^4 yields coefficient -1/64 on u^3 n^6 after the exterior factor; the sixth difference is therefore -45/4. Multiplication by s^(-2) cannot make an earlier term reach degree six. Substitution u = A t + O(t^2) and h^2 = w0 t^3 + O(t^4) gives the displayed -45 A^3 w0/4 contribution.

At s = 1 the h^2 coefficient is a_n = n(n-1)(n-2)/8. The h^4 coefficient before taking the logarithm is

`E[d^4/24 - m d^2/4 + m^2/8 + d^2/3 - m/4]`.

Using E S_n^2 = n and E S_n^4 = 3n^2-2n, only d^4/24 reaches n^6 and its coefficient is 1/128. The logarithmic subtraction a_n^2/2 has the SAME coefficient 1/128. The surviving h^4 logarithmic coefficient consequently has degree at most five and its sixth difference is exactly zero. Analyticity makes the nearby coefficient O(u). The remaining terms O(u^7 + h^2 u^4 + h^4 u + h^6) are O(t^7) under the source scaling. These estimates concern the finite set n <= 6 and the fixed bounded analytic bank, not a uniform all-arity expansion.

## Preserved bank and sign

The previously constructed bank has A = (1,y,z,z), gamma = p(-1,-2,1,2), and w0_i = A_i^3/6 - 2 gamma_i. Summing the new cell coefficient gives

`K_delta = -15(1+y^6+2z^6)/16 + (45p/2)(-1-2y^3+3z^3)`.

At delta = 0, y = 1 and p = (1+z^4)/(72(z-1)), this reduces to `(15/16) P6(z)` with P6(z) = -z^6+z^5+z^4+z^2+z-1. The inherited simple root lies in (9/5,19/10). Direct hand checking gives P6(9/5) = -9046/15625. On that interval,

`P6'(z) = z^3(-6z^2+5z+4)+2z+1 <= -102369/3125 < 0`.

Thus K0 < -13569/25000 < -1/2. Analytic continuity permits ONE fixed sufficiently small positive delta satisfying this strict margin together with every earlier strict arm and diagonal-IFT constraint. The source bank is not retuned by root count, connector placement or t.

Actual source diagonals multiply across the chronological word, so their logarithms add exactly. Every ordinary connector and padding factor contributes a quadratic polynomial in n to the log diagonal and has zero sixth difference. The higher coefficients of w(t) affect the displayed expression only at order t^7. The two factors use the SAME preserved bank and therefore contribute `2 K_delta t^6 + O(t^7) < 0`.

Their diagonals through five are exactly those of ordinary passage E(ab), by the prior actual construction. Consequently the sixth difference of the product is exactly `log b6(product) - 15 log(ab)`. For all sufficiently small positive t,

`0 < b6(product) < (ab)^15`.

The accepted cap-five return thus fails to be an ordinary return at cap six. Moving the previously allowed connectors or pads, or changing higher analytic weight coefficients while retaining this leading bank, cannot remove this sixth-diagonal defect. A different leading bank would at least have to satisfy the new necessary condition `sum_i A_i^3 w0_i = (sum_i A_i^6)/12`, equivalently `sum_i A_i^3 gamma_i = (sum_i A_i^6)/24`, as well as the other actual diagonal and full-forest equations. This condition alone constructs no source return.

## Legal observable separation and limits

The final witness was checked against the original admitted-testers ALL-CAP source, including its explicit pendant construction. Insert the two alternatives into the A pendant of the same positive ((A,B),(C,D)) exterior, keep every other source parameter fixed, and use six A copies, six B copies, one C copy and one D copy. The allowed A/B restriction event is the topology with the specified six (A_i,B_i) cherries. A within-pendant A-only or B-only merger before their meeting is incompatible with this event. Once the roots meet, the same ordinary Kingman topology factor applies in both alternatives. The event probability is a common strictly positive rational topology constant times the fixed B-pendant six-root survival times b6 of the A alternative. The strict b6 inequality therefore changes an actual permitted final-topology probability on fourteen labelled copies. No route bit, hidden root count or intermediate no-merger record is added to the observation menu.

This accepts separation of the particular preserved cap-five source family from ordinary passage at six roots. It does not construct a cap-six return, bind a prescribed GIVEN conjugator C, prove an all-cap source membership statement, provide an unknown-source-size stopping rule, or close original G4. Other banks and architectures remain separate.

The review used hand mathematics and read-only source/Git/JSON identity inspection. No mathematical program, symbolic system, numerical extraction, source evaluation, compiler, harness, Actions polling or API experiment was run. The exact author proofs and historical cap-five receipts are unchanged; only this owned review and authentication record are published.
