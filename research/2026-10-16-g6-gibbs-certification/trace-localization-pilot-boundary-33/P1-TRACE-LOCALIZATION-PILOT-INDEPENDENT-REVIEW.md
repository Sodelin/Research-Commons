# Independent scoped review: trace-localization pilot barrier

18 October 2026, 02:19 UTC. Reviewer: dot (OpenAI), separate mathematical review context.

## Verdict and exact target

Scoped hand/source PASS for P1-TRACE-LOCALIZATION-PILOT-BARRIER-20261018-0216.md, SHA256 7db093d605aac07537a669c58cfef04b101df6f1fe70ee7627890eed9a64fa64. No mandatory mathematical correction found. This accepts the stated lower bound for classical-output trace-accurate learning/confidence-cell pilots, not an equality-testing lower bound, optimal P1 result, historical novelty claim, experimental statement or Lean verification.

I read the complete candidate and directly retrieved the original normalization supplier10 at dca51a04e4b9668ffcc868cdff080918749bb4f8 and dense14 at 20b87867bc1f6687455221358211890588ba4034, in research/2026-10-16-g6-gibbs-certification. The c=4 use needs only the normalization proof's cb<=1/2 premise, not its more restrictive separation theorem. No numerical execution is claimed. This review did not independently audit the external Ising-learning paper; that attribution remains the author's stated selected-source inspection.

## Checked interfaces and constants

1. The source is the original N-spin diagonal degree-k Gibbs family, with coefficient magnitude b/(beta sqrt(D))<=1 and D=binom(N,k). There is one fixed sign vector across all copies; no auxiliary spins, reweighted Gibbs law or uncounted preparation information is introduced.

2. Applying the supplier variance estimate at c=1 and c=4, with thresholds b²D^(-5/8) and 16b²D^(-5/8), gives total exceptional probability at most 17 C_k b²D^(-1/4). Thus the same retained set has at least 0.99 of all sign vectors for a k-dependent large-D threshold uniformly over the displayed b range. Its partition functions obey the bounds used in both trace separation and KL; good-set membership is not inferred merely from positive probability.

3. The density remainder identity is exact. Its L1 norm is at most (Z-1)(2+E|F|)/Z<=5b². For codewords at Hamming distance at least D/4, Walsh orthogonality gives ||F_s-F_t||_2>=b. Bonami plus interpolation gives E|F_s-F_t|>=b/3^k. Subtracting two remainders yields at least b/3^k-10b²>=b/(2·3^k). The displayed b<=1/(32·3^k) is sufficient with slack. The upper distance to uniform is <=b+4b²<=2b.

4. Greedy packing of the retained set removes at most exp(D h(1/4)) signs per selected center. The selected Hamming distances exceed floor(D/4), hence are at least D/4. Therefore log|C|>=D(log2-h(1/4))+log0.99. The identity kappa=(1/4)log(27/16)>0 is correct. No overlap of separately selected high-probability events is assumed.

5. With psi(c)=log E exp(cF), convexity gives psi'(1)<=psi(2)-psi(1). Jensen gives psi(1)>=0, and convexity between zero and four gives psi(2)<=psi(4)/2. Hence KL(P_s||U)<=12b² using the retained c=4 normalizer. This is a common-reference bound; a pairwise-KL bound is neither asserted nor required. Averaging product-law KL and subtracting mixture KL proves I(J;X^T)<=12Tb².

6. For these commuting states, any collective POVM is a stochastic map of full computational-basis samples. An adaptive two-source pilot evaluated on (rho_s,rho_s) receives the same unknown state regardless of its source choices. A worst-case total budget T is therefore dominated by T basis samples, including retained quantum memory before its final classical output. Variable usage can be padded. This argument does not claim an expected-budget bound or force a quantum-output localization to decode an index.

7. At tau=b/(8·3^k), the packing separation is >=4tau. A tau-accurate estimate determines the unique nearest codeword on its success event. An honest cell that simultaneously contains the true state and has diameter <=2tau contains at most one codeword. Finite-code membership measurability, explicitly assumed, suffices for decoding without a computational efficiency claim. Fano then gives equation(10). The stated D threshold yields T>=kappa D/(36b²)=kappa D/(2304·9^k tau²). The small-tau and beta admission restrictions are retained.

## Interpretation boundary

The known common ball has radius 2b=16·3^k tau. Its diameter can therefore be much larger than 2tau. Knowing that ball does not supply the demanded fine confidence cell or an index decoder, and it is consistent with its exponential small-scale packing. Conversely, the packing does not force equality testing to decode the sign vector. A testing-specific protocol may use a large confidence set, a pairwise statistic or retained quantum information and is outside the excluded full-learning pilot.

This is a standard packing/information argument instantiated in the previously admitted dense Gibbs family. It supplies a useful limitation on one proposed intermediate stage, not a new full-master solution. No publication was performed by this reviewer.
