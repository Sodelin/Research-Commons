# Rejected shortcut: multiply scalar per-epoch expectations

30 October 2026. Hand calculation, not a new Lean theorem. This rejects a proposed implementation shortcut; it does not refute the scientific finite-window theorem.

Take the admitted two-copy single-population Kingman source, with unordered merger rate λ=8/3. Use one balanced nonzero JC character column: both leaf charges are the same nonzero element of (Z/2)^2. Before coalescence the total nonzero-charge count is 2, so the normalized JC killing coefficient is κ=(4/3)*2=8/3. After coalescence the merged charge is zero.

Let T~Exp(λ) be the actual merger time. The finite-epoch scalar occupation expectation with terminal payoff 1 is

    W(t) = E[exp(-κ min(T,t))]
         = exp(-(λ+κ)t) + λ/(λ+κ) (1-exp(-(λ+κ)t))
         = 1/2 + (1/2) exp(-(16/3)t).

Set t = 3 log(2)/16 > 0. Then W(t)=3/4 and W(2t)=5/8, whereas W(t)*W(t)=9/16. They differ by 1/16.

Two consecutive epochs with identical population/rate and the identity boundary describe the same actual process as one interval of length 2t. Multiplying W(t) by a freshly initialized W(t) incorrectly forgets whether the original lineages already merged during the first interval. This is precisely the information retained by the actual endpoint-resolved weighted kernel. The correct decomposition is:

- first interval's unmerged weighted mass exp(-(λ+κ)t)=1/2, followed by the two-lineage W(t)=3/4;
- first interval's merged weighted mass λ/(λ+κ)(1-exp(-(λ+κ)t))=1/4, followed by the one-lineage weight 1;
- total (1/2)*(3/4)+(1/4)*1=5/8.

All rates, charges, shared-genealogy semantics and the identity boundary are inside the retained contract. This is not an arbitrary scalar counterexample. It demonstrates why the later scalar renewal draft must be strengthened to actual exit-state indicators before finite-calendar composition or exact S/E/F/M counting. No frozen candidate states the false product identity.

Scope source: [retained finite-pulse contract](https://github.com/Sodelin/Research-Commons/blob/f96399576168328322aab80f1193afaaf4312fef/research/2026-10-05-dot-flouri-clock-jc-conjecture-resolution-0908z/bridge/CONTRACT.md). This note uses only its two-copy, one-population, positive-rate and identity-boundary subcase; it makes no assertion of full formal admission of the wider catalogue.
