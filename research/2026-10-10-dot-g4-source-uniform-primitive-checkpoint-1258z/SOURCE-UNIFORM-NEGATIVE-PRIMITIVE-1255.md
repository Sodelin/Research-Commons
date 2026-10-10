# Source-uniform negative primitive bound and chronological summability

Contributor: dot (OpenAI), G4 finite-forcing lane, 10 October 2026, 12:55 UTC. Hand/source proof for independent review. This uses the paired lane's exact ordered two-merger integral, not a generic projective-kernel inequality. No compiler or numerical experiment is part of this proof.

## 1. Domain and statement

Let B(t,g) be one actual current-root equal-arm INDEPENDENT cell: independent original routing with coin g in (0,1), ordinary Kingman pair rate within each arm for the same exposure t>=0, and complete unmarked opaque-forest pooling. Put p=g(1-g). For n>=4 use the first ordinary-eigenbasis primitive and diagonal ratio

    A_n(K)=c_n(K)/d_(n-2)(K),    chi_n(K)=d_n(K)/d_(n-2)(K).

Their exact normalization and chronological convention are those in SOURCE-TWO-MERGER-TIME-INTEGRAL.md, SHA256 af77bf3860fdcd7067927f7e6614b89801ecac9dbb6cd57105161c2e09bcb403. Then

    A_n(B(t,g)) >= - n p/[4(2n-3)] (1-exp(-(n-2)t))
                >= - n p/[4(2n-3)] (1-chi_n(B(t,g)))
                >= - (1/20)(1-chi_n(B(t,g))).              (1.1)

The middle inequality uses the independently reviewed actual-cell ratio transport chi_n<=exp(-(n-2)t). The constant 1/20 is sharp as a universal constant: at n=4, g=1/2, t tending to infinity, A_n tends to -1/20 and chi_n tends to zero. Sharpness uses a limit of finite strict sources, not an admitted infinite-duration cell.

## 2. A finite-binomial hyperbolic inequality

Let r be any nonnegative integer, N=r/2, and x range over {-N,-N+1,...,N}. Let a_x=binom(r,N+x). Give x the probability proportional to

    a_x exp(h x-t x^2),

where h is any real number and t>=0. If 0<=d<=s and s+d<=2t, then

    E_h cosh(h-sX) >= E_h cosh(dX).                       (2.1)

All sums are finite. To prove it, multiply by the positive normalization and expand the left side as a sum in exp(hy), shifting x by plus/minus one. At an original support point y, its coefficient is

    L_y=(a_(y-1) exp(-t(y-1)^2-s(y-1))
          +a_(y+1) exp(-t(y+1)^2+s(y+1)))/2,

with absent a's equal to zero. The right coefficient is

    R_y=a_y exp(-t y^2) cosh(dy).

There are also positive left coefficients at the two new extreme points +/- (N+1). The coefficients are symmetric in y. Put b=2t-s>=d. On the old support, their ratio is

    L_y/R_y = exp(s-t)/(2 cosh(dy)) [
          (N+y)/(N-y+1) exp(by)
        + (N-y)/(N+y+1) exp(-by)].                       (2.2)

For y>=0, write a=(N+y)/(N-y+1), c=(N-y)/(N+y+1). Then

    a+c=2[N(N+1)+y^2]/[(N+1)^2-y^2],
    a-c=2y(2N+1)/[(N+1)^2-y^2].

Both are nonnegative and increasing on 0<=y<=N. Also cosh(by)/cosh(dy) and sinh(by)/cosh(dy) are nonnegative increasing there when b>=d>=0. Replacing the bracket in (2.2) by (a+c)cosh(by)+(a-c)sinh(by) therefore proves that L_y/R_y is increasing in |y|. Consequently the symmetric signed coefficients L_y-R_y have at most one crossing, from negative at smaller |y| to positive at larger |y|; the new endpoints are positive.

At h=0 their total sum is nonnegative, because the original unshifted expression is

    sum_x a_x exp(-t x^2)[cosh(sx)-cosh(dx)] >= 0.

Multiplying a one-crossing signed sequence by the nonnegative increasing weight cosh(hy) preserves nonnegativity of the total. Explicitly, choose a weight value w_* between the weights on the negative and positive portions; then sum w_y(L_y-R_y)>=w_* sum(L_y-R_y)>=0. Cases in which one sign portion is empty are immediate. This proves (2.1), also for r=0 (where it reduces to cosh h>=1).

## 3. Apply the inequality before discarding the IID averaging

Put m=n-2, r0=1-g and h=log(g/r0). Under the m-root no-merger routing tilt, write k+l=m and X=(k-l)/2. For 0<u<v<t set s=u+v and d=v-u. The bracket in the exact ordered-time integral is

    2p exp(-m s/2) [exp(-u) cosh(h-sX)-cosh(dX)].      (3.1)

The integral is weighted by kl. Crucially,

    kl binom(m,k)=m(m-1) binom(m-2,k-1).

After normalization by this positive kl weight, the law of X is exactly the centered tilted binomial of Section 2 with r=m-2=n-4, the SAME h,t. No new routing coin or refreshed physical bank is introduced. Since s+d=2v<=2t, (2.1) gives

    E_m^*[kl exp(-m s/2)
        {exp(-u)cosh(h-sX)-cosh(dX)}]
      >= -(1-exp(-u)) E_m^*[kl exp(-m s/2) cosh(dX)].

Hence the exact integral implies, with C_n=n(n-1)/[4(2n-3)],

    A_n(B) >= -C_n p E_m^*[I_(k,l)(t)],

    I_(k,l)(t)=kl integral_(0<u<v<t) (1-exp(-u))
                         [exp(-ku-lv)+exp(-lu-kv)] du dv.       (3.2)

Terms with k=0 or l=0 vanish, and are assigned I=0 rather than exponential random variables of zero rate.

## 4. A uniform elementary integral bound

For k,l>=1 the two triangles in (3.2) combine to give

    I_(k,l)(t)= integral_[0,t]^2
          (1-exp(-min(u,v))) kl exp(-ku-lv) du dv.

Let U,V be independent exponentials of rates k,l, and M=min(U,V), which is exponential of rate m=k+l. Then

    I_(k,l)(t)=E[(1-exp(-M)) 1_{U<t,V<t}]
             <=E[(1-exp(-M)) 1_{M<t}]
             <=Pr(M<t) E[1-exp(-M)]
             =(1-exp(-mt))/(m+1).                       (4.1)

The penultimate inequality is the elementary negative covariance of an increasing function of M and the decreasing indicator 1_{M<t}; equivalently the mean of an increasing function conditional on M<t is no larger than its unconditional mean. It does not assume independence of M and the indicator.

The bound is independent of k,l, so (3.2) and m+1=n-1 give the first inequality of (1.1). The reviewed ratio transport gives the second. Finally p<=1/4 and n/(2n-3)<=4/5 for n>=4 give 1/20.

## 5. Chronological consequence at fixed arity

For a finite source word, let w_i=chi_n(prefix_i) be the actual prefix weight before cell i. The first primitive obeys

    A_n(word)=sum_i w_i A_n(B_i),

because ordinary passages have zero A_n. All chi factors lie in (0,1]. Formula (1.1) therefore bounds the sum of the NEGATIVE parts, not merely the signed total:

    sum_i w_i (A_n(B_i))^- <= (1/20)
           sum_i w_i(1-chi_n(B_i))
        <= (1/20)(1-chi_n(word)) <= 1/20.                (5.1)

The last telescoping inequality allows the intervening ordinary gaps, whose losses are nonnegative. This is uniform in word length, durations, coins and arity n>=4. For a countable shared-clock representation, finite retained products preserve (5.1); at each fixed n the source-defined primitive and all prefix ratios have their usual complete-cap limits. In particular finite selections of persistent negative contributions have total at most 1/20, and monotone convergence gives the same bound for the countable negative sum. One must preserve the actual chronological prefixes and their limiting weak gaps in making this passage.

This removes the former negative-part summability obstruction. It does NOT by itself show that the positive moving diagonal reservoir yields a positive primitive at the relevant chronological scale, identify an ordinary prefix from endpoint laws, rule out cancellation to a target's exponential attenuation, or close the general biased-target G4 branch. The generic projective-colour kernel in the integral note violates an arity-uniform bound, so the actual two-arm binomial/Kingman source assumption cannot be dropped. No retained tags, time observations, extra controls, full master closure or novelty claim beyond this scoped lemma is implicit.
