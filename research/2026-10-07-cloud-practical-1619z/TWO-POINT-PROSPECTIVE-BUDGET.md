# A sufficient future budget for distinguishing the retained source pair

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane. Hand-derived standard Hoeffding argument with a bounded exact arithmetic certificate, 7 October 2026. Independent review pending; no Lean proof or new observations.

For the two already authenticated original source points, **69,134 fresh iid complete loci suffice for a fixed AA1 midpoint test with worst-source error below 1/20**, conditional on the original source law and prospective procedure being admitted. This is a sufficient bound, not a lower bound on needed samples. It is about 67.5 times the archived count of 1,024. It does not establish full-domain localization or success on the archived record.

The source points and shifted Bernoulli mean enclosures are reused from the [frozen actual receipt](covariance-points-attempt1/RESULT.json), SHA256 `8acf47eadbb01e220f9ebb87746b64f070a0f527bfc0a230e58b316e9f3c6931`. They are the same original source vector with rA = 1 and rA = 13/10; all other coordinates coincide. The earlier authenticated original forward provider supplied these enclosures. This calculation makes no provider call, extracts or replays no data and shifts no means again.

For each feature, interval subtraction bounds its actual absolute mean gap. AA1 has a certified positive lower gap

    g = source1_AA1_lower − source0_AA1_upper
      = 11254380792373651910475 / 1208925819614629174706176
      ≈ 0.009309405597740666.

Its upper gap is `5627190396186825955241 / 604462909807314587353088`. Every other feature has absolute gap upper at most `5 / 1208925819614629174706176`, strictly smaller than g. Thus AA1 is rigorously the largest actual scalar mean gap among the original nine features for these two points. The certificate preserves all nine comparisons rather than inferring equality from overlapping enclosures.

Fix AA1 before future observations. Write b for the source0 AA1 mean upper and c for the source1 AA1 mean lower, and fix threshold

    t = (b+c)/2
      = 1644622734721637346836787 / 2417851639229258349412352.

After exactly N fresh original complete loci, choose source1 if their AA1 average is at least t; otherwise choose source0. The actual source0 mean is at most b and the actual source1 mean is at least c, so each wrong decision requires a one-sided sample-mean deviation of at least g/2. The original AA1 feature lies in [0,1]. Standard one-sided Hoeffding therefore gives, under either of these two source hypotheses,

    P(wrong decision) ≤ exp(−2N(g/2)^2) = exp(−N g^2/2).

The established inequality is attributed to Hoeffding, *Probability inequalities for sums of bounded random variables*, JASA 58 (1963), 13–30, Theorem 2, [DOI](https://doi.org/10.1080/01621459.1963.10500830); no fresh primary-source reread is claimed here. Independent complete loci are required. Dependence between sites, phased copies and other features within a locus is unrestricted because the test uses one fixed scalar per locus. The risk is the maximum of the two source-conditional misclassification probabilities; no simultaneous two-source tail union is needed because only one source generated a given future record.

The [exact arithmetic certificate](two-point-budget-attempt1/RESULT.json) proves

    748933/250000 < log(20) < 149787/50000.

For the upper bound q, the positive partial sum `sum_(k=0)^20 q^k/k!` exceeds 20. For the lower bound p, `sum_(k=0)^20 p^k/k! + (p^21/21!)/(1−p/22)` is below 20: subsequent exponential-series term ratios are at most p/22. These rational comparisons enclose the logarithm without evaluating a transcendental equality.

Taking `N = ceil(2*(149787/50000)/g^2) = 69134` ensures `N g^2/2 ≥ 149787/50000 > log(20)`, hence error below 1/20. At N = 1,024, the corresponding exponent is about 0.04437, below the certified logarithm lower bound, so **this sufficient Hoeffding inequality does not certify 1,024**. It does not prove the midpoint test fails at 1,024 or that 69,134 is necessary. This is the specified rA source pair, with no uniform guarantee for other pairs in D and no change to accepted near-collision limitations.

The [bounded arithmetic script](check_two_point_budget.py) completed PASS under CPU 5 seconds, wall 10 seconds and 256 MiB, recording 0.0011 seconds elapsed. Source SHA256 is `f33c1d921362e3ff50651b4e794b9a5dfb47602c422e997c3924091954992c9d`; receipt SHA256 is `786408a74ccdc06cac96a005be7ac67a50ab7038d58b83a8588b873921c466a6`. It creates its output directory exclusively; reproduction must preserve archived evidence. This is an arithmetic proof check, not a sampling experiment or an empirical performance measurement.

The feature, threshold, fixed N and separate future risk must be settled before fresh observations. No old-process intersection, archived confidence issuance, biological admission, new sampler or budget for actual sampling is supplied. The original full nine-parameter, all-normalized-width-at-most-1/20 endpoint remains open.
