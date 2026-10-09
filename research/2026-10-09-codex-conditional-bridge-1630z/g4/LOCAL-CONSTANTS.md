# Exact quantitative bounds for the conditional local certificate

Contributor: Codex G4 computation lane. Hand derivation tied to
`local_constants` in the new module. This expands the reviewed provider's
effective-bound step for rational target parameters. It does not establish
its missing all-rival neighbourhood premise or an original observation
producer. No Lean proof or full real-algebraic RCF engine is claimed.

Let `theta=(p,y)`, `y=1/q`, `0<p0<1/4`, `1<y0<Q=1/c`. Each genuine cell has
`w=p(y-1)>0` and, under the same observed positive COMMON clock, `y<Q`.
Write `phi_n=log R_n`. The exact polynomial recurrence for
`g^k+(1-g)^k` is `s0=2,s1=1,s_k=s_(k-1)-p s_(k-2)`.
Pairing the binomial terms therefore builds `R_n(p,y)` without algebraic
coin evaluation. Polynomial division checks the reviewed identity

```text
R_n=1+w D_n(y)+w² E_n(p,y),  D_n(y)=n Σ_(j=0)^(n-2) y^j.
```

For any polynomial `P=Σ c_ij p^i y^j`, define the exact coefficient bound
`B(P)=Σ |c_ij|(1/4)^i Q^j`. It bounds `|P|` on the entire source rectangle.
Put `e_n=B(E_n)`, `d_n=D_n(Q)` and
`L_n=e_n+(d_n+e_n)²/2`. For `0<w<=1`, the actual `x=R_n-1>=0` satisfies
`x<=w(d_n+e_n)`. The elementary log inequality in the reviewed provider
gives `|phi_n-wD_n|<=L_n w²`. For separator coefficients a and exact positive
Bernstein lower bound d, put

```text
Hweak=Σ |a_n| L_n,
epsilon=min(1,d/[2(Hweak+1)]).
```

Then each weak extra contributes `a·phi >= d w-Hweak w² >= d w/2`.
Summing uses `Σ w_i² <= epsilon Σ w_i`; no count-dependent constant occurs.

Choose an initial rational max-norm radius

```text
h=min(p0/2,(1/4-p0)/2,(y0-1)/2,(Q-y0)/2,1).
pmin=p0-h, pmax=p0+h, ymin=y0-h, ymax=y0+h.
w0=p0(y0-1), wmin=pmin(ymin-1)>0.
R2max=1+2 pmax(ymax-1), R3max=1+3 pmax(ymax²-1).
```

Suppose exact diagonal matches hold and let `S=Σ w_i` over extras.
For n=2,3, positivity and `log(1+x)<=x` give

```text
|phi2(body)-phi2(target)|<=2S,
|phi3(body)-phi3(target)|<=3(Q+1)S.
```

The mean-value bound for exp between those two endpoints gives
`|R2-R20|<=2 R2max S` and `|R3-R30|<=3 R3max(Q+1)S`.
Use the exact inverse

```text
w=(R2-1)/2, y=(R3-1)/(3w)-1, p=w/(y-1).
```

Algebraic subtraction, with denominators bounded below on the initial
rectangle, proves

```text
|w-w0|<=R2max S,
|y-y0|<=Cy S,
Cy=R3max(Q+1)/wmin+(R30-1)R2max/(3wmin w0),
|p-p0|<=Cp S,
Cp=R2max/(ymin-1)+w0 Cy/[(ymin-1)(y0-1)],
Cinv=max(Cy,Cp).
```

Every `R_n>=1` on the whole source rectangle. Thus each Hessian entry of
`log R_n` has absolute bound

```text
B(d_i d_j R_n)+B(d_i R_n) B(d_j R_n).
```

Let H be the maximum over the four Hessian entries of their sums weighted
by `|a_n|`. The certificate checks `a·d_p phi(theta0)=0` and
`a·d_y phi(theta0)=0` exactly. Taylor's formula along the convex body
rectangle therefore gives

```text
|a·[phi(body)-phi(target)]|<=2 H |theta-theta0|_infinity²
                              <=C3 S²,
C3=2 H Cinv².
```

This is the same tangent space as the duration derivative:
`d_t=y d_y`. Neither log evaluations nor floating Hessian samples enter the
checker. Coefficient norm bounds are conservative but exact.

The n=2 match also makes S small from body closeness alone. Each extra
satisfies `log(1+2w)>=2w/(1+2epsilon)`. Direct subtraction of the body's
`R2=1+2p(y-1)` and the 1-Lipschitz bound for log on `[1,infinity)` give

```text
S <= Bbody eta,
Bbody=(1+2epsilon)[(ymax-1)+pmax].
```

The code selects

```text
eta=min(h,d/[8(C3+1)(Bbody+1)]).
```

Hence `S<d/[8(C3+1)]`. If any strict extra exists, then `S>0` and the exact
full-N diagonal match would imply

```text
0=a·[phi(body)-phi(target)]+Σ a·phi(extra)
 >= dS/2-C3 S² >0,
```

a contradiction. Therefore no extras exist; the exact two-coordinate
inverse identifies the body's p,y. The body and weak conditions are
explicit premises about actual physical sources. The constant derivation
does not certify that all arbitrary fitting rivals satisfy those premises,
recover ordinary pads, prove full-forest equality, or extend an
INDEPENDENT-only menu to BOTH.
