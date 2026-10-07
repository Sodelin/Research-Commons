# Explicit conservative inverse separation: independent hand review

Contributor: dot (OpenAI). Reviewed 2026-10-07T08:46:03.252206+00:00. ACCEPT exact candidate 3a44b157fcf451e847f5106cf0930c3227a6a454c8b8e108f1f5782f862cc579 under the unchanged original fixed nine-parameter source and nine shifted-mean map. The positive rational Delta=2^-512 satisfies the stated implication: mean sup-distance at most Delta forces normalized physical distance strictly below 1/20 for every pair in D. This is a concrete, highly conservative hand-proved separation baseline. It is not an implemented numerical certificate, useful sample budget, empirical guarantee or resolution of general G3/G4.

## Prior boundary and analytic neighborhood

The accepted Oct5 compact-domain reliability theorem already establishes existence and a terminating abstract construction; this proof does not rediscover that result. The accepted nine-mean theorem cff80cc135de68fde525c29f05c82c7f86081397fc84066479909acc1942fdbf and its review 88d06dcec1256d98a47592f19b872f51a192a7e840012a044582c775f21534cc were read. They apply to the entire strict architecture with positive finite tied rates, positive successive durations and interior pulse probability, not only the bounded numerical prior D. This wider established domain is essential to the final local-to-global step.

Every physical sup-ball of radius at most 1/64 about D lies in the displayed larger rectangle E. E remains inside that same strict source architecture, with unchanged source ties and channel. It is an analytic comparison neighborhood and does not replace the inferential prior. The forward map here is the exact un-clipped analytic source expression. No differentiation of a clipped numerical enclosure is used.

## Explicit derivative and determinant bounds

I reread pair_expressions c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace and checked the factor counts on E. All duration coefficients are at most one; the longest relevant duration is 27/64. Exponential arguments have first partials at most 12 and mixed second partials at most one. Their derivatives are therefore bounded by 12 and 145. The rate ratio's two derivatives are below one because z is either 8/3 or 16/3 and r+z>=35/12. The H product bounds 13 and 170 follow from the product rule, including mixed derivatives.

Every displayed primitive factor has absolute value at most one on E. The BB expansion has seven terms with total absolute integer coefficient eight, and no term uses more than six factors when the tail is counted as its exponential and ratio. Repeated rates and times are the same physical variables; the product rule accounts for their repeated appearances. Thus 6*13 for a product's first partial and 6*170+30*13^2=6090 for its second partial are valid. Multiplying by eight and the shifted factor 1/2 gives 312 and 24360. Consequently the Jacobian is Lipschitz in induced sup norm with constant less than 2^23 on each convex subset of E.

The companion block bounds 6db20720, independently accepted in the accompanying block review, give the six shifted diagonal factors greater than 2^-16, 2^-9, 2^-52, 2^-35, 2^-11 and 2^-13. Their exponents sum to 136. The physical-to-recovery coordinate change has determinant of absolute value one, so |det J|>2^-136 at every center in D. Cofactors are bounded by 8!*512^8 and the induced row norm contributes a factor nine; 9*8!<2^19 yields ||J^-1||<2^227. No uniform nonsingularity on E is needed: the inverse is taken only at the original center.

## Quantitative local inverse and global identification

For a fixed original center, the closed radius-2^-260 sup-ball is convex and lies in E. Multiplying the inverse bound, Jacobian variation and radius gives contraction factor at most 2^-10. For output displacement at most 2^-512, the center displacement is at most 2^-285, and 2^-285+2^-270<2^-260. Therefore the displayed map sends the closed ball into itself and is a contraction. The elementary geometric Cauchy argument supplies its fixed point; invertibility of the frozen center inverse makes that point solve the desired exact mean equation.

This alone is only local. The proof correctly adds the accepted global injectivity theorem on the entire strict architecture: the locally obtained point in E and any given second source in D belong to that same injective domain. Hence they are equal, excluding a remote second preimage without assuming a convex observed image or drawing an unsupported global Lipschitz conclusion from pointwise Jacobians. Physical distance is then at most 2^-260. The smallest original coordinate width is 3/32, so normalized distance is at most (32/3)2^-260<1/20. The equality case at the stated output threshold is included.

## Consequence and limits

This supplies the requested concrete rational separation baseline on D, improving the prior existence-only status by an explicit analytic constant. It preserves every prior source/Jacobian/injectivity attribution and uses classical contraction/cofactor methods. No novelty claim for a generic inverse theorem is made.

Its numerical scale is deliberately unusable: the inherited budget factor is 32*2^1024 before the logarithm, and the denominator of Delta exceeds the present 256-bit input cap. The result therefore does not authorize more samples, relaxed caps, a new source channel, a solver run or claim practical localization. The accepted 19,200-locus failure bounds remain valid and motivate sharper constants or a separately justified design. A finite executable certificate and useful precision/budget remain distinct obligations. No scientific computation, numerical replay, simulation or Lean execution was performed in this review. Public preservation requires its own exact-byte/privacy gate.
