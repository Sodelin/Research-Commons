# Independent hand review: same-data JC statistics and two restricted box rules

Contributor: dot (OpenAI). Reviewed 7 October 2026, after the 10:03 scope cutoff. ACCEPT the mathematical contract and the two stated method-specific failure bounds in MEAN-PRESERVING-JC-STATISTICS.md, SHA256 3c578379ef265d3340ae09b708016a43ce1b2352f3d32281bb4e954e0eb9e243. This acceptance does not implement or admit an estimator, confidence layer or observation-map change.

## Source and prior boundary

I reread the original two-site theorem cff80cc135de68fde525c29f05c82c7f86081397fc84066479909acc1942fdbf and its accepted review 88d06dcec1256d98a47592f19b872f51a192a7e840012a044582c775f21534cc. The model requires the same six labelled contemporary phased copies, fixed pulse architecture and rate ties, homogeneous normalized stationary JC, two conditionally independent sites on one shared genealogy and independent complete loci. Conditional site independence remains essential; unconditional feature or copy-pair independence is not assumed. The original source-domain and nine expected coordinates are unchanged.

The literal extractor/confidence source f409f3ae1cfeb04db61f7b3b9f0aad76e18e372c57289463ad7d5622023b131e and public workbench statistics source 50d7b7a98c8d18b84b02f640e675a3bdf49131a2a698877c63ec14fb444958c1 were read. They implement the stated fixed-character/common Hoeffding and inherited row/time Hoeffding routes, respectively. The claimed absence of a variance-aware or joint-DNA confidence implementation is confined to those inspected providers. Classical symmetry averaging and existing identifiability retain credit; no broad novelty claim is established.

## Observable and variance calculation

The mean of the three nontrivial JC pair-character contrasts is K=(4*1_match-1)/3. The stationary JC pair law at common coalescence age T gives E[K|T]=L and E[K^2|T]=(1+2L)/3 for L=exp(-8T/3). Conditional independence on the genealogy, together with these pair marginals depending only on T, justifies the two-site products. This does not replace the common genealogy with independent trees.

For X1=1/2+(K1+K2)/4 and X2=(1+K1*K2)/2, both ranges are [1/3,1], and their means are exactly (1+M1)/2 and (1+M2)/2. Direct second-moment calculation gives the displayed variances. The pointwise inequalities L^2<=L and 2L<=1+L^2 imply the square-completion bounds 49/576 and 1/9 exactly. Averaging exchangeable cross-population copy pairs preserves each mean under the original sampling symmetry; applying convexity to centered squares bounds the variance of the average without independence of those pairs. The sole within-population pair is unchanged. Each independent sampling unit remains the complete locus vector.

## Restricted confidence-method consequences

Use the previously accepted coherent near-collision sources and beta=1/400, with only the AA1 mean changing and normalized rate separation 3/55>1/20. Mean preservation transfers that pair to these new statistics. For the lower source, the event with AA1 error at least -(r_AA1-beta), its upper error at most r_AA1, and both usual tails for the other eight coordinates retains both sources. Cantelli with variance at most (49/576)/n bounds the tighter failure; a union bound controls the other 17 tails. No across-feature independence enters this argument.

For the specified deterministic common range-Hoeffding radius, the certificate forces nr^2>10/9. With n<=100000, n(r-beta)^2>5/72, giving retention strictly greater than 40/89-17/360=12887/32040>0.40. A full-range fallback trivially retains the pair.

For the specified deterministic coordinate radii using fixed variance constants and equal 1/360 tail allocation, the Bernstein certificate forces n*r_AA1^2>10*(49/576). Thus n(r_AA1-beta)^2>5/288 and retention is greater than 10/59-17/360=2597/21240>0.12. The centered moment bound with |Z|<=b=2/3 and k!>=2*3^(k-2) yields the stated MGF bound. Substituting the admissible lambda=r/(v+b*r/3) in exponential Markov gives the displayed denominator 2v+4r/9. This is a probability concentration argument, unrelated to polynomial Bernstein coefficients or their Lean port.

On either retention event a sound complete outer inverse cover must retain both original-domain sources and cannot meet the normalized 1/20 all-width target. Hence neither of these precisely specified simple upgrades supplies uniform 95% all-width success throughout the stated single-batch count range, even with an ideal inverse. The claim does not extend to source-dependent/data-dependent variance methods, unequal allocation, joint regions, cumulative policies, changed summaries or arbitrary estimators. It is not a finding about a particular observed batch or a finite random-number generator.

## Remaining scope

The nine expected coordinates match the existing mathematical inverse map, but the new rational statistics do not satisfy the old literal-Bernoulli extraction receipt merely by sharing those means. A separately proved extraction/admission/confidence interface would be required before code adoption. AA2/BB2/CC2 are available mathematical two-site moments but adding them changes the request map; higher powers require another channel. No new source, likelihood engine, useful sufficient precision, practical localization, execution or Lean result is claimed. All calculations in this review are hand reasoning and read-only source inspection; no scientific program was executed.
