# P1: aggregate trace localization can already cost full learning

18 October 2026, 02:16 UTC. Author: dot (OpenAI), working with Nolan.

**Local mathematical route assessment for review.** This is a packing/Fano consequence of the previously reviewed dense Gibbs normalization supplier. It is not a new equality-testing lower bound, an optimal P1 theorem, a novelty determination, or a Lean proof. No numerical experiment is needed or claimed. The candidate is not independently accepted merely because its suppliers were reviewed.

## 1. Question and conclusion

The original P1 problem retains two unknown N-qubit Gibbs states at fixed beta>0, locality at most k, every nonidentity Pauli coefficient bounded in magnitude by one, unrestricted degree and incident strength, equality versus full trace-norm separation at least epsilon, and a worst-case TOTAL copy budget allowing collective measurements and adaptive source choices.

The preceding Fisher-geometry assessment showed that some statistically ill-conditioned directions have negligible trace effect. That leaves a legitimate possibility: localize in trace metric, discard only directions whose aggregate effect is small, and use a task-specific collective test. The calculation below rules out one overly strong version of that plan.

For each fixed k>=3 and sufficiently small trace accuracy tau>0, a pilot that outputs a classical trace-accurate state estimate, or an honest confidence cell of full trace diameter at most 2 tau, can require

    Omega_k(binom(N,k)/tau^2)

copies. This remains true when the unknown state is promised to lie in one known small trace ball around the maximally mixed state. All physical spins are the original N spins; no reservoir or auxiliary cost is hidden.

Thus a uniformly trace-accurate learning stage already has the N^k exponent of the accepted general upper, up to logarithms. This does not exclude a weaker localization, a large confidence set equipped with a useful test, or a collective protocol retaining quantum memory. Nor does it prove that P1 equality testing needs this many copies.

## 2. Exact admitted family and reused supplier

Fix k>=3, D=binom(N,k), and

    0 < b <= 1/(32*3^k),       beta >= b/sqrt(D).

For each sign vector s in {−1,+1}^D, let

    a=b/sqrt(D),
    F_s(x)=a sum_(|S|=k) s_S product_(i in S) x_i,
    Z_s=E_U exp(F_s),
    P_s(x)=U(x) exp(F_s(x))/Z_s,
    H_s=−F_s/beta.

Here U is uniform on the N-spin cube. The diagonal density matrix rho_s has diagonal P_s. Every physical coefficient has magnitude b/(beta sqrt(D))<=1. Fixed beta>0 satisfies admission for all sufficiently large N. The sign vector is fixed before every copy.

The exact normalization supplier is [note10](https://github.com/Sodelin/Research-Commons/blob/dca51a04e4b9668ffcc868cdff080918749bb4f8/research/2026-10-16-g6-gibbs-certification/DENSE-UNTILTED-GATES-10.md), used with c=1 and c=4 as checked in [note14](https://github.com/Sodelin/Research-Commons/blob/20b87867bc1f6687455221358211890588ba4034/research/2026-10-16-g6-gibbs-certification/DENSE-CONVEX-TRUNCATION-LOWER-14.md), Sections1–3, and its [separate assistant-context hand review](https://github.com/Sodelin/Research-Commons/blob/816c3e66f1de3f35a5bc19fce1ceda2ef16f2d96/research/2026-10-16-g6-gibbs-certification/DENSE-LOWER-14-INDEPENDENT-REVIEW.md). Their historical candidate headers are qualified by the linked later review.

In detail, put B_c=cosh(ca)^D, eta=b^2 D^(−5/8), eta_4=16b^2 D^(−5/8), and

    G={s: |Z_s/B_1−1|<=eta and |Z_(4s)/B_4−1|<=eta_4}.

The supplier gives

    |G|/2^D >= 1−17 C_k b^2 D^(−1/4),   C_k=4*3^k.       (1)

For all sufficiently large D depending only on k, this is at least 0.99, uniformly over the displayed b range. For every s in G,

    1 <= Z_s <= 1+2b^2,
    Z_(4s) <= exp(8b^2)(1+16b^2),
    E_U F_s=0,   E_U F_s^2=b^2.                          (2)

No unconditioned high likelihood moment or prior testing lower bound is used here.

## 3. Aggregate trace separation, not coordinatewise neglect

Set R_s=exp(F_s)−1−F_s>=0. Its U-mean is Z_s−1. Consequently, writing f_s=P_s/U,

    f_s−1−F_s = [R_s−(Z_s−1)(1+F_s)]/Z_s,
    E_U |f_s−1−F_s| <= (Z_s−1)(2+E_U|F_s|)/Z_s
                      <= 2b^2(2+b) <= 5b^2.             (3)

If s,t have Hamming distance at least D/4, then orthogonality gives

    ||F_s−F_t||_2 = 2a sqrt(Hamming(s,t)) >= b.

For every degree-at-most-k Boolean polynomial f, the standard Bonami fourth-moment bound and interpolation give

    E|f| >= ||f||_2/3^k.

Using this for F_s−F_t and then (3),

    ||rho_s−rho_t||_1
      = E_U|f_s−f_t|
      >= b/3^k−10b^2
      >= b/(2*3^k) =: Delta.                            (4)

The final inequality uses b<=1/(32*3^k), with slack. Every member also satisfies

    ||rho_s−U||_1
      <= [E_U|F_s|+2(Z_s−1)]/Z_s
      <= b+4b^2 <= 2b.                                  (5)

Thus the entire separated packing will lie in one KNOWN trace ball of radius 2b around U. The radius is independent of N.

For comparison, changing only one coefficient sign changes F by at most 2a pointwise. The partition-function ratio then lies between exp(−2a) and exp(2a), so the density ratio lies between exp(−4a) and exp(4a). The single-flip trace distance is at most exp(4a)−1, tending to zero as D grows. Equation(4) proves directly that many individually small coordinate changes can nevertheless have a nonvanishing aggregate trace effect. No conversion of an ill-conditioned Fisher inverse is involved.

## 4. Exponentially many separated points

Greedily select points of G, removing after each choice the Hamming ball of radius floor(D/4). Distinct selected signs then have distance greater than floor(D/4), hence at least D/4. The standard binomial entropy bound is

    sum_(j=0)^floor(D/4) binom(D,j) <= exp[D h(1/4)],
    h(p)=−p log p−(1−p)log(1−p).

It follows by applying the binomial Chernoff bound at p=1/4, or directly by weighting each binomial summand with p^j(1−p)^(D−j). Therefore a selected code C exists with

    log |C| >= kappa D + log(0.99),
    kappa=log 2−h(1/4)=(1/4)log(27/16)>0.               (6)

This also yields a trace-metric covering obstruction. A ball of radius strictly below Delta/2 cannot cover two code points. Even the known ball (5) therefore requires exponentially many such smaller balls. It does not follow that testing requires identifying which point is present.

## 5. Information per physical copy

For s in G let psi_s(c)=log E_U exp(cF_s). This is a finite smooth convex function with psi_s(0)=0 and psi_s(1)>=0. The KL divergence to U obeys

    KL(P_s || U)=psi_s'(1)−psi_s(1)
       <= psi_s(2)−2psi_s(1)
       <= psi_s(2)
       <= (1/2)psi_s(4)
       <= 4b^2+(1/2)log(1+16b^2)
       <= 12b^2.                                       (7)

The first inequality is the convex secant bound between1 and2; the second uses Jensen; the third is convexity between0 and4; the last two use(2) and log(1+x)<=x. This common-reference KL estimate avoids an unproved pairwise KL bound.

Draw an index J uniformly from C once, and observe T independent samples from P_J. For their joint law X^T,

    I(J;X^T) <= (1/|C|) sum_s KL(P_s^T || U^T)
              <= 12 T b^2.                             (8)

The first inequality follows by subtracting the nonnegative KL of the mixture to U^T from the average displayed KL. Any data processing or independent algorithmic randomness cannot increase the mutual information.

All rho_s commute in a known basis. A general collective POVM on T copies is therefore a stochastic map of T complete computational-basis samples: its outcome probabilities are obtained from the diagonal entries of its effects. This also covers sequential adaptive measurements, their retained quantum memory and final classical outputs, because the whole procedure defines one POVM on the supplied copies.

For a two-source pilot, choose the legal null pair (rho_s,rho_s). Every source choice now returns the same state. A worst-case total budget T gives at most T independent basis samples; unused samples can be padded. Hence(8) holds for that whole adaptive two-source experiment. The budget is not an expected stopping-time convention.

## 6. What a trace-small pilot would cost

Suppose a classical-output pilot succeeds with probability at least2/3 for every admitted source by returning either:

- an estimate hat-rho with ||hat-rho−rho||_1<=tau; or
- a classically specified confidence set containing rho and having full trace diameter at most2tau on the same success event.

For the confidence-set formulation, membership of each member of a fixed finite reference family is assumed measurable from the output; no efficient membership algorithm is required. This is a statistical confidence-set claim, not an arbitrary inaccessible label for an unknown set.

Choose

    tau=b/(8*3^k),
    equivalently b=8*3^k tau,
    0<tau<=1/(256*9^k).                                (9)

Then Delta=4tau. Nearest-code-point decoding of an estimate succeeds whenever its error is at most tau. A successful confidence set has at most one code point and contains the true one, so it too decodes J. Thus the induced index error is at most1/3.

For completeness, the elementary entropy form of Fano gives

    H(J|output) <= log2 + Pr(error) log|C|,
    I(J;output) >= (2/3)log|C|−log2.

Combining(6)–(8) proves

    T >= [(2/3)(kappa D+log0.99)−log2]/(12b^2).         (10)

For D >= [3log2−2log0.99]/kappa, this implies the convenient explicit bound

    T >= kappa D/(36b^2)
      = [kappa/(2304*9^k)] D/tau^2.                    (11)

The normalization good-set threshold from(1) and physical admission beta>=8*3^k tau/sqrt(D) must hold as well. They do hold eventually for each fixed k, fixed beta>0 and tau in(9). The constants are not claimed uniform in growing k, nor is this a claim for every large trace radius.

## 7. Prior work and exact interpretation

This is a conventional packing/Fano learning argument, using the already-reviewed dense Gibbs supplier. The closest directly inspected primary precedent is Devroye, Mehrabian and Reddad, *The minimax learning rates of normal and Ising undirected graphical models*, [arXiv:1806.06887v3,3 June2020](https://arxiv.org/html/1806.06887v3), Theorem1.3, Lemma2.2 and Section4.1. Its Ising learning rate is proportional to sqrt(m/T) for m edges without fields; its sign packing and small interaction magnitudes give the same parameter-count learning obstruction for k=2. The paper uses TV equal to half the full L1 norm. Here the k>=3 consequence is derived explicitly from our retained degree-k family; no historical-novelty claim is made.

The prior source was checked at those exact statements and the displayed lower-family construction, not audited in full. Its expected-risk theorem is not silently converted into this high-probability claim: Section6 gives the required probability-level argument directly.

This result does not overturn any accepted P1 lower bound or supply a matching full-class testing upper. Classical learning can be harder than equality testing. A proposed source-adaptive scheme may still retain a large confidence set, discard directions with a proved AGGREGATE trace budget, or estimate only a pairwise decision statistic. Its guarantees must cover the actual replicated two-source experiment uniformly, with all pilot/measurement-selection copies counted. No such scheme with a better worst-case rate is established here.

## 8. Exact next obligation

The useful remaining positive target is a copy-only, task-specific localization or comparison theorem that preserves enough evidence to distinguish equality from full trace distance epsilon, controls the total error contributed by discarded directions, and improves on the accepted M-scale collective net bound without first producing a uniformly trace-small classical confidence cell. Here M=sum_(j=1)^k 3^j binom(N,j). It must include arbitrary noncommuting coefficientwise-bounded Gibbs states and charge all copies used to learn or select the measurement.

The known local trace ball in(5) already has order-D metric complexity. Merely replacing parameter distance by trace distance does not remove this aggregate complexity. Equations(10)–(11) restrict full-learning pilots; they do not prove that the weaker testing-specific target is impossible.

Main was verified at8a3908bdb236a08e0fdf7cee23728e8e32bc51d2 at the start of this pass. No public or Google Doc update was made.
