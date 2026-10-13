# Why pointwise private forcing and faithful fixed exteriors do not imply whole-source forcing

Contributor: Codex whole-source subagent, 13 October 2026. **Exact abstract counterexample to a proposed proof implication.** This is not a coalescent/reticulate source and not a G4 impossibility result. Its purpose is to specify the additional uniform fibre obligation required by a whole-source argument.

Consider a class of private response sequences indexed by finite positive integers, together with one distinguished target. Each coordinate is the success probability of a Bernoulli observation. Define

```
x_0(k) = 1/2                         for all k>=1,
x_n(k) = 1/2+1/(4n)                  for 1<=k<=n,
x_n(k) = 1/2+1/(2n)                  for k>n,        n>=2.
```

All probabilities are strictly between zero and one. The first coordinate is different for every private source x_n and for x_0. Consequently **every private target is finitely forced by its first coordinate against the entire private class**.

Let a one-dimensional exterior parameter theta range over the compact interval [1/3,2/3], contained in the strictly positive probability domain. Its response action is

```
C_theta(x)(k) = theta x(k).
```

For every fixed theta the map on every capped response vector is injective, with a positive scalar triangular diagonal theta. It uses the same theta at all coordinates. It is polynomial, positive and cap-preserving; no cancellation, zero parameter or unbounded exterior dimension is needed.

Fix the single full target (theta_0,x_0)=(1/2,x_0). Its response is 1/4 at every coordinate. For each n>=2 take

```
theta_n = n/(2n+1),   private source x_n.
```

Then theta_n belongs to [1/3,2/3], and one exact physical tuple in this abstract model gives

```
C_(theta_n)(x_n)(k) = 1/4                      for k<=n,
C_(theta_n)(x_n)(k) = 1/4+1/[4(2n+1)]          for k>n.
```

Thus after every finite legal coordinate set the same fixed full target has an exact inequivalent finite-index rival: choose n at least its largest index. In particular, even compactness and a positive lower bound on all exterior diagonals do not repair the transfer.

The example invalidates the generic implication

```
private pointwise finite forcing
 + finite-dimensional / compact unknown exterior
 + capwise faithful every fixed exterior
 => full target finite forcing.
```

A general G4 proof must use additional facts of the actual source family. For example, it could identify an adequate exterior response map from legal data, obtain a uniform forcing statement on its full nuisance-parameter fibre, derive a positive source inequality controlling private complexity, or otherwise prove that the abstract adjustment above cannot occur. The [fixed-exterior tomography theorem](FIXED-EXTERIOR-OBSERVABILITY.md) establishes none of those additional assertions for a changing rival exterior.

The abstract response family does not assert genealogical projectivity, forest grafting, original graph admission, natural BOTH compatibility or finite Kingman source realizability. It therefore cannot serve as the required fixed admitted-target all-prefix counterexample for G4. This distinction is part of the result, not a missing detail to assume.

The calculation is elementary exact rational algebra and has not been submitted as machine verification or historical novelty. No test execution is needed to replace the displayed exact identities.
