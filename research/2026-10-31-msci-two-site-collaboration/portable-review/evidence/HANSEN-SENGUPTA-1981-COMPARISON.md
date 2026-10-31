# The 1981 interval enclosure and the manuscript's target-box extension

## Sources and reading boundary

On 31 October 2026 UTC, I read the [publisher's article record and abstract](https://link.springer.com/article/10.1007/BF01933165) for Eldon Hansen and Saumyendra Sengupta, “Bounding solutions of systems of equations using interval analysis,” *BIT Numerical Mathematics* 21, 203–211, June 1981, DOI `10.1007/BF01933165`. The publisher presents the body as subscription content; I did not obtain that body from the publisher.

A separate web result supplied extracted text of a [university-hosted reproduction](https://www.math.rug.nl/~gert/documents/2010/interval/hansen_sengupta.pdf) whose first page has the same title, authors, volume, pages and abstract. I read the extracted text of §§2–4, especially printed pages 204 and 206, equations (2.3)–(2.4) and (4.1)–(4.4). The browser reported a cached crawl rather than an authenticated publisher download. A screenshot request for the page containing (2.4) returned a reference but no inspectable image payload, so the equation comparison is **text-extraction based**, not a visual audit. No original PDF bytes were retained, authenticated or hashed. The publisher record and university copy are two routes to the same named article, not independent mathematical results.

## Comparison

On printed page 204, the 1981 authors present a nonparametric Krawczyk enclosure for a root of `f`, using a box `X`, a point `x`, an interval Jacobian `J(X)` and a preconditioning matrix `B`:

```
K(X) = x - B f(x) + (I - B J(X))(X - x).
```

They describe `x` as the midpoint and `B` as an approximation to the inverse midpoint Jacobian in their setup. Their later method on printed page 206, equations (4.3)–(4.4), instead uses a successive interval-Newton update. The paper therefore discusses related but distinct operations; it does not identify the displayed Krawczyk box with the complete successive method.

The MSci manuscript uses an **uncertain target box** `O`, an outward enclosure `Fq` of the model's `F(q)`, an interval enclosure `J` of the derivative on the complete source box `C`, and an arbitrary fixed rational matrix `Y`:

```
K(C,O) = q - Y(Fq - O) + (I - YJ)(C - q).
```

Substituting `f_a(x)=F(x)-a` for each fixed `a in O` explains the shared algebraic pattern. The manuscript's pointwise argument must separately justify preservation of **every** `x in C` with `F(x) in O`, for any fixed `Y`, including `Y=0`. The 1981 paper's midpoint and approximate-inverse setup alone does not establish that target-box generalization, existence of a compatible source, contraction, a verified implementation or the MSci forward-map assumptions. Interval evaluation order can affect computed widths even for algebraically related formulas.

The 1981 paper cites R. Krawczyk's earlier article as its reference 9. I also checked only the [publisher's record and abstract for that 1969 paper](https://link.springer.com/article/10.1007/BF02234767): *Computing* 4, 187–201, DOI `10.1007/BF02234767`. I did not read or translate its full body; the displayed formula above is attributed to the accessible 1981 reproduction, not to an independently checked equation in the 1969 body. This is a bounded source comparison, not a historical-priority determination or a Lean proof.
