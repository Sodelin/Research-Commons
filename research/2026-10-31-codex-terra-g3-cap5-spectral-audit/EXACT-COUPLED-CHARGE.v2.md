# Exact cap4/cap5 source-charge comparison with actual chronology

Contributor: Codex Terra, 31 October 2026. This is a derived exact use of
the saved cap4 charge and the actual cap5 Q-band source. The equal-arm
polynomial identity is checked over Q[q,beta] by the separately preserved
`check_cap5_bare_channels.v3.py`; the chronological identity below is hand
algebra. It is not a positivity theorem for the whole fibre, an action or
phase bound, or original G3/G4 closure.

## Single actual source cell

Let B=B(q,q,g), with 0<q<1, 0<g<1, v=g(1-g),
beta=(2g-1)^2, d=1-q. The OLD cap4 source charge and the actual cap5
source in `PROOF-AND-OVERLAP.md` satisfy EXACTLY

    chi(q,beta)=(v/3)d^2[d-(5+q)beta],
    A5(q,beta)=a(q) chi(q,beta)-D5(q,beta),
    a(q)=3q(q^2+3q+1)/10,
    D5(q,beta)=q v beta (q+1)d^4/5 >= 0.                    (1)

This uses one physical coin and arm survival; neither source is separately
chosen. Equation (1) implies A5<=a(q)chi for every strict cell. In
particular A5>0 forces chi>0, but a chi-positive cell need not have A5>0.
At the nontrivial chi=0 locus, D5>0 and A5=-D5<0. The source factor and
its stricter positivity threshold appear in the main cap5 audit; the
same-source retained-e review separately exhibits a nonzero e there.

For `s(C)=v(beta^2 u^3+beta u^4+u^5)`, u=-log q,

    0 <= D5 <= (2/5) v beta u^4 <= (2/5) s(C).             (2)

This is a source comparison, not an assertion that the globally weighted
signed terms in a word are individually nonnegative.

## Exact whole-word equation

Write the actual word as its bare cells and ordinary factors. For the i-th
bare cell define the full chronological weights

    W42_i=product_(f before B_i) b4(f) * product_(f after B_i) b2(f),
    W52_i=product_(f before B_i) b5(f) * product_(f after B_i) b2(f),
    R_i=W52_i/W42_i=product_(f before B_i) b5(f)/b4(f).

The shared suffix is exact. Every factor, including every ordinary gap,
occurs in its original position. Each R_i is positive and nonincreasing;
no clock replacement or factor reordering is used.

Retain the fixed reference

    S=E(t) B(x,x,1/2) E(b),
    x=t/(2-t), b=t^2(2-t),
    k_r=b_r(K), s_r=b_r(S),
    C4=(k2-k4)/(s2-s4), C5=(k2-k5)/(s2-s5).

Complete cap5 commutation supplies both exact endpoints

    sum_i W42_i chi_i = t^6 b C4 chi_*,
    sum_i W52_i A5_i = t^10 b C5 A5_*,
    A5_*=a(x)chi_* > 0.                                    (3)

The second line is oriented as an A5-normalized receiver. Its raw Q-band
coefficient tau52 is `-(5/3)A5`, hence is negative on the fair reference.
All denominators in C4,C5 are positive, and k4,k5 retain their actual
unknown source values.

Substituting (1) into (3) and subtracting `t^4 a(x)` times the first
equation gives the EXACT signed identity

    sum_i W42_i [R_i a(q_i)-t^4 a(x)] chi_i
      - sum_i W52_i D5_i
        = t^10 b a(x) chi_* (C5-C4).                        (4)

This is an all-finite-word identity, including different actual source
weights and the exact reference endpoint. It is not derived by applying
the bare-cell relation directly to the whole word. On the existing cap12
fibre, the inherited source-cost theorem and (2) give the coarse bound

    0 <= sum_i W52_i D5_i <= (2/5) sum_i s(C_i) = O(H h^4).

The remaining weighted chi sum and C5-C4 are signed/unknown. The paired
clocks fix k2 but not k4 or k5, and (4) does not bound them by reference
powers. No inference to an O(h^6) action, complement sign, phase or
integer witness follows without a new coupled full-fibre estimate.

The right side is not universally nonnegative, even on the ACTUAL complete
fibre. For any fixed H=(log 2)/m and integer N>=2, choose h=H/(4N)
and the intended strict reference power K=S(t)^N. Then

    C_j=(s2^N-sj^N)/(s2-sj)
       =sum_(ell=0)^(N-1) s2^(N-1-ell) sj^ell.

The reference has 0<s5<s4<s2, and this polynomial is strictly increasing
in sj. Therefore C5<C4. The right side of (4) is strictly negative,
although all cells are fair and every D5_i is zero. This prevents a simple
sourcewise nonnegative-sign argument for that side. It does not establish a
universal sign or exclude a different coupled estimate.

The symbolic checker replay completed with exit 0. This revision and its
checker are bound by `SHA256SUMS.v4.txt`. The preceding cap5 proof, its
parent review, the prior coupled-charge note and manifests, and the
retained-e review were not altered.
