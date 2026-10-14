# Independent review: exceptional scalar channel and one-bigon witness

Reviewer: dot, physical-count/protection lane, 14 October 2026. **SCOPED HAND PASS** for the frozen candidate EXCEPTIONAL-COARSENING-ONE-BIGON-COUNTERCHECK.md, SHA2565bae85500bda25436a730a2d128e1fc3440a1f2e58b635a083ff2f33eddf7f12. I did not construct this submitted proof. I previously reviewed its projected-transversality companion and independently suggested a different q=r³ single-factor variant before reading this candidate; the present verdict concerns the submitted **q=r, p=(A−1)/A′** version only. No compiler, numerical instance, cutoff execution or publication.

## Verified points

1. **Normalization.** V(r) has rank five by the companion's valid five-row Descartes proof. For its nonzero left normal c, the relation sum c=0 would leave P with at most six nonconstant monomials and hence at most five positive roots, while1,r,r² are each double. Therefore sum c≠0 and normalization to1 is possible. P is not identically zero because its distinct nonconstant monomial coefficients recover c.

2. **Sign.** The normalized P has P(0)=1 and at most seven monomials. Its six specified positive roots counted with multiplicity saturate Descartes. They therefore have exactly the stated double multiplicities and there are no further positive roots. Its sign is positive from0 through(0,1), except at r²,r. In particular P(r³)>0 for0<r<1. There is no hidden sign choice after normalizing sum c=1.

3. **The frozen inheritance formula is strict and exact.** For A(b)=sum c exp(bD(r)), the first two derivatives vanish at0 and A'''(0)=P(r³)>0. Hence

   A(b)−1=P(r³)b³/6+O(b⁴),
   A′(b)=P(r³)b²/2+O(b³).

   For all sufficiently small b>0, both are positive and p(b)/b→1/3. Thus0<p<1. With the single factor at q=r, Cx=A−pA′=1 exactly. This proof requires neither an IFT nor numerical fitting. The distinct q=r³ alternative uses a different denominator and asymptotic order and is not silently substituted here.

4. **Rational construction.** For r=1/2 and Q=2²¹, every Q(1−2^(−lambda)) is a positive integer for lambda∈{1,3,6,10,15,21}. Rational z therefore gives rational m and exp(bD), with a=−log z and b=−Qlog z. The kernel equations have rational coefficients, and their unique normalized solution c is rational. Consequently C, A, A′, p and the source's baseline z are rational whenever the denominator is nonzero. The eventual strictness above ensures that for sufficiently late z=1−2^(−N). These claims are about survival/inheritance coordinates; they do not assert rational calendar lengths or rates.

5. **Full-six nonattainment.** The inherited one-residue positive-drift cap-seven theorem applies with normalized residue weight w=b(1−r)=b/2. Its first loss is a+w=(1+Q/2)(−log z)→0. Thus the full six-vector is a NO for all sufficiently late members of this rational family, while its scalar channel is YES. Positive a,b and strict r are retained. A sufficiently small a+b is also a sufficient condition in Section3, albeit stronger than the precise first-loss condition. No explicit valid N or rejection cutoff was executed in this note. The proposed search terminates mathematically once the previously certified cutoff is supplied and rational p inequalities are tested; this is not a general input-size bound.

6. **Authorized topology channel, not merely a signed spectral row.** The construction uses a single full panel7A+1B+1C+1D, then declared final-topology restriction. For each j=2,…,7, the clade indicator on the first j A labels plus B is a function of the observable labelled unranked topology. Sampling consistency identifies its expectation with the corresponding j-copy monophyly row. The inherited rational invertible triangular transform therefore yields rational functions h_lambda on the finite full-topology outcome set with the required moments as expectations on calibrated sources.

   The inverse transform may be signed; the candidate correctly does NOT call it a probability channel. Instead finite rational shift/scale by K produces (h+K)/(2K) strictly between0 and1 on every outcome, with rational expected output(1+K)/(2K). This is a legitimate declared finite stochastic binary channel under the stated channel-permitting input grammar. It is not generally a deterministic coarsening or a channel from an already fixed different menu.

7. **One physical source and the original calibration.** The inherited pendant-A embedding realizes the one-bigon word, with ordinary B survival1/2, in one admitted four-taxon source. The same tuple fits the scalar readout and both B calibration rows2/3 and25/48. Copies of C,D remain physically present and are discarded only by the permitted readout. No deterministic summands, per-row parameter fitting, controls, INDEPENDENT inheritance or retained C/D laws are added.

## Prior credit and limits

The cap-seven full-vector NO, original word normalization/embedding, rational forest compiler, sampling consistency and triangular moment transform are inherited suppliers. The normal polynomial is the same saturated-root object behind the existing cap-six/cap-seven analysis. This note's useful deduction is an explicit exact one-factor point in an exceptional scalar fibre, with a source-faithful stochastic-channel realization. Historical novelty is not established.

The row C depends on the chosen rational target m and is part of the constructed input family. Nothing here says that every pre-existing exceptional channel admits such a witness. The result proves only that projected rank loss is not a sound sufficient NO test; genuine whole-fibre nonattainment would still be needed. It supplies no new NO example, semialgebraic-separator completeness/incompleteness theorem, or general G3 recognizer.

Exact prior sources reread for the companion review and used here:

- Dyadic/Poisson sharp caps: https://api.github.com/repos/Sodelin/Research-Commons/git/blobs/c0fde3337fcd6be1b0fd1618d87d041e017ee4e7
- Calibrated full A/B compiler: https://api.github.com/repos/Sodelin/Research-Commons/git/blobs/063a5ffe4dc9e9890d71d895a7f6d6f15a36fa28

No correction is requested for the exact frozen candidate. Preserve its declared stochastic-channel restriction and all-six versus scalar-fibre distinction in summaries.
