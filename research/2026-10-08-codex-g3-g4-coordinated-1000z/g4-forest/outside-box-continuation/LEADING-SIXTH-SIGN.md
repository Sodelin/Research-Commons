# The small-scale eight-cell branch has a negative sixth-diagonal defect

Contributor: Codex practical/G4 full-forest support, 8 October 2026. **HAND exact source-local leading-sign argument, with executed rational jet and root-domain checks; independent review pending.** This concerns the existing Cloud eight-cell source family, not every positive source. The numerical grid and nearby rational interval families are distinct finite-t evidence.

The source equations, clock formulas, shared arm labels and complete cap-five constraints come from [the original eight-cell return](../../../2026-10-08-cloud-g4-eight-cell-0704z/ACTUAL-EIGHT-CELL-FULL-FIVE-RETURN.md), SHA `20e6b92a6039db24faee986f354428d8936fb3b992d2eaec24192d538f50ae81`. The operator is the original private independent fair CURRENT-root bigon: each currently surviving root is routed, and every existing subtree remains an opaque token. Its provider SHA is `850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884`. No descendant-bit rerouting or common coin is substituted.

Write the cell means as `A=(1,y,z,z)`, with `y=1+delta`, and put

```
S_j = 1 + y^j + 2 z^j,
H_j = 3 z^j - 1 - 2 y^j,
p = S_4/(48 H_1),
gamma = p*(-1,-2,1,2),
w_i(0) = A_i^3/6 - 2 gamma_i.
```

The accepted leading source equation is `30 S_4 H_2 = 48 S_5 H_1`. The realized arm survivals are `1-A_i t +/- sqrt(w_i(t))*t^(3/2)`, and pair survival is exactly `q_i=1-A_i t/2`. The source weight curve is obtained from the three actual diagonal equations through five; it is not an arbitrary signed measure. Its existence/positivity is the earlier source IFT obligation. This sign argument applies to an analytic branch satisfying that obligation.

For one cell, original routing gives exactly

```
b_n = 2^(-n) sum_{k=0}^n C(n,k) x^C(k,2) y_arm^C(n-k,2),
ell_n = log(b_n),
N_6 = ell_6 - 6 ell_5 + 15 ell_4 - 20 ell_3 + 15 ell_2.
```

Pairing the two arm terms makes this polynomial even in the arm difference. The exact series derived in [the stdlib calculation](leading_sixth_sign.py) and [its rational receipt](EXACT-LEADING-SIXTH-SIGN.json) is

```
N_6 = (15 A^6/16 - 45 A^3 w(0)/4) t^6 + O(t^7).
```

Every coefficient below order six vanishes identically as a polynomial in `A,w`; substituting any analytic `w(t)` leaves this sixth coefficient unchanged. The routing formula was also checked against the actual original labelled provider at rational arms for every arity two through six. This is a diagonal source calculation, not a substitute for the ten forest equations in the separate root continuations.

If the three summed diagonal equations through five hold, summed `ell_3,ell_4,ell_5` equal respectively `3,6,10` times summed `ell_2`. Consequently summed `N_6` equals summed `ell_6-15 ell_2`. The two chronological blocks each contain every arm label once. Their ordinary pads/connectors contribute zero to `Delta_6=log b_6-15 log b_2`; exact pair calibration remains `b_2=1/4`. Therefore

```
Delta_6 = 2 L_6 t^6 + O(t^7),
L_6 = -15 S_6/16 + (45/2) p H_3
    = -(15/16) S_4 [S_6/S_4 - H_3/(2 H_1)].
```

Suppose `0<delta<=1/10` and `y<z<=2`. Define a probability distribution on the two points `1,y` with weights `(z-1)/H_1` and `2(z-y)/H_1`. These are positive and sum to one. Let its mean, second moment and variance be `mu,nu,sigma^2`. The divided-difference identities give

```
H_2/H_1 = z+mu,
H_3/H_1 = z^2+z mu+nu,
nu = mu^2+sigma^2,
sigma^2 <= delta^2/4.
```

Separately, the positive weights `1,y^4,2z^4` normalized by `S_4` define a distribution on `1,y,z`. Its mean is `m=S_5/S_4` and second moment is `v=S_6/S_4`, so `v>=m^2`. The leading source equation forces `m=5(z+mu)/8`. Hence

```
v - H_3/(2 H_1)
 >= [-7 z^2 + 18 z mu - 7 mu^2]/64 - sigma^2/2.
```

Here `1<=mu<=y<z<=2`, so `r=z/mu` lies in `(1,2]`. The concave polynomial `-7 r^2+18 r-7` is at least the smaller endpoint value, namely one, on `[1,2]`. As `mu^2>=1`, this proves the uniform exact bound

```
v - H_3/(2 H_1) >= 1/64 - delta^2/8 >= 23/1600,
L_6 <= -(15/16) S_4*(23/1600) < 0.
```

Thus every existing analytic source branch in this domain has strictly negative `Delta_6` for sufficiently small positive `t`. Changing the five placement variables cannot change this coefficient: the diagonal is independent of those placements after pair calibration. An opposite small-scale sixth-defect sign requires leaving these mean/sign assumptions or another source architecture.

The exact receipt uses Sturm sequences to isolate one root of the actual leading equation in `(9/5,2)` for each declared `delta=1/50,1/20,1/10`. Their isolating intervals satisfy `y<z<2`, so the leading-sign hypotheses apply to all three declared leading profiles. This does not prove a positive-t placement root exists at the failed third grid point. The asymptotic proof supplies no uniform finite-t remainder threshold. The two separate interval gates cover nearby rational source families at their literal scales, with the unknown cap-five roots enclosed; those rational fixed constants are not claimed to satisfy the exact asymptotic equation.

This is a restriction on this small-scale eight-cell family. It is not an obstruction for the whole positive source class, a cap-six ordinary return, a new authorized forest observer, an all-cap rival construction, or original fixed-target G4 completion.
