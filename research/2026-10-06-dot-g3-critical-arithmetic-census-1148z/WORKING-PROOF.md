# Effective height bounds for unknown rational critical residues

Contributor: GPT-6 Astra research lane, 6 October 2026. NEW candidate hand argument, independent review pending. This is a finite critical-presentation census, not an actual-source recognition theorem. No height-bound, residue enumeration, critical-point isolation or RCF run on an observation input has been executed.

## 1. Exact statement and what prior work lacked

Use the six full COMMON cap-seven coordinates indexed by n=1,3,6,10,15,21. Write Lambda_n=n, H(p,q)_n=-log(1-p+p q^n), and R_n(r)=1+...+r^(n-1). All logarithms are real logarithms of positive numbers.

Input is a positive effectively real-algebraic tuple m and an integer N>=0. Consider ALL presentations

    -log m = a Lambda + sum_(i=1)^k H(p_i,q_i) + w R(r),
    a>0, w>0, 0<r<1, k<=N,

in which every strict pair (p_i,q_i) is critical for the paired normal c(r), and r is rational but is NOT supplied. The pairs and multiplicities are also unknown. There is an input-computable finite list containing every such presentation, with r and all pairs algebraic and a,w specified by exact real logarithmic expressions. In particular the rational denominator of r is input-effectively bounded.

The old all-residue critical-finiteness theorem handled every SUPPLIED algebraic r and gave the safe degree bound 2495. The old Baker/projective theorem excludes algebraic-irrational r in a critical presentation of algebraic m. Neither alone gives a height bound for an unknown rational r. The new proposed step uses a primitive multiplicative base and height growth to produce that bound, including unknown retained factors.

This statement has no transcendental-residue conclusion. A critical presentation may itself be actually realizable; the accepted two-copy saddle examples explicitly show why passing this census is not a NO certificate.

## 2. Exact inherited polynomial bounds

Use P0(r,p,q), Q(r,p,q)=Q0/(1-p), and the integer polynomial row B(r) from the accepted all-residue theorem. Degrees are

    deg_r P0, deg_r Q <=49,
    deg_p P0=5, deg_p Q<=4,
    deg_q P0<=56, deg_q Q<=55.

The padded Sylvester determinant T(r,q)=Res_p(P0,Q) has deg_r<=441 and deg_q<=499. Its specialization T(r,q) is NOT identically zero in q for any 0<r<1, by the old two-slice/positive-gcd certificate. At every strict q, P0 is a nonzero degree-five polynomial in p. Those are the actual no-exception premises, rather than generic elimination assumptions.

Let ||.||_1 mean sum of absolute integer coefficients. Choose an integer L>=1 bounding ||P0||_1 and ||Q||_1. It can be computed without expanding a resultant. If S=sum_i||B_i||_1 and S_lambda=sum_i lambda_i||B_i||_1, the safe choice is

    L=max(1, 486 S, 1215 S_lambda).

Indeed each f_i=1-p+p q^lambda has coefficient norm at most3. The P0 bound is 2*3^5*S. Q0 has norm at most3^5*S_lambda, and division of its degree-five p polynomial by 1-p increases coefficient norm by at most5. Hence ||T||_1<=9! L^9 by the determinant expansion.

Put c=bitlength(2*9!*L^9), ell=bitlength(2L). These integer bounds exceed the corresponding natural logarithms.

## 3. Height bounds for all retained factors

Here h is the absolute logarithmic Weil height. Classical facts used are h(xy)<=h(x)+h(y), h(x/y)<=h(x)+h(y), h(x+y)<=h(x)+h(y)+log2, and h(x^j)=|j|h(x). For a root alpha of a nonzero polynomial with algebraic coefficient vector A, the elementary local root bound gives

    h(alpha)<=h_projective(A)+log2.

At a nonarchimedean place use max(1,|alpha|)<=max_i |a_i/a_d|; at an archimedean place insert a factor2, then sum and use the product formula. This supplies the stated projective coefficient bound even if the polynomial is reducible. Evaluation of integer polynomials of degree at most d in r and e in q gives coefficient-vector height at most d*h(r)+e*h(q)+log(coefficient norm). The vector is required to be nonzero.

Write r=A/B in lowest terms with 0<A<B. Then h(r)=log B. For any strict critical pair the old resultant and nonzero P0 imply

    [Q(p,q):Q]<=499*5=2495,
    h(q)<=441 log B+c,
    h(p)<=49 log B+56 h(q)+ell
         <=24745 log B+56c+ell.                    (H)

The projective coefficient vectors used here cannot vanish: T_r is nonzero, and the p^5 coefficient of P0 is -d(r)*product_n(1-q^n), nonzero on the strict domain. No unknown exceptional denominator is being omitted.

For f_n=1-p+p q^n,

    h(f_n)<=2h(p)+n h(q)+2log2.

Consequently one factor contributes at most

    h(f_21)+21h(f_1)
      <=44h(p)+42h(q)+44log2
      <=1107302 log B +44(56c+ell)+42c+44.        (F)

Choose an integer H0>=1 greater than h(m_21)+21h(m_1), computable from minimal-polynomial coefficient bounds. Let

    C0=H0+N*[44(56c+ell)+42c+44],
    C1=1107302*N.

After dividing the unknown product of at most N retained factors, the drift-normalized algebraic numbers beta_n satisfy

    beta_n=(m_n/product_i f_(i,n)) /
                 (m_1/product_i f_(i,1))^n >1,
    h(beta_21)<=C0+C1 log B.                    (U)

All five beta_n lie in a common number field of degree at most

    D=delta*2495^N,

where delta is the degree of a number field containing all input coordinates. Neither the field itself nor the factors must have been found to use this degree upper bound.

## 4. A primitive exponent cannot hide the denominator

For n=3,6,10,15,21 define the homogeneous integer polynomial

    P_n(A,B)=sum_(j=0)^(n-2)(n-1-j) A^j B^(n-2-j),
    e_n=B^(21-n) P_n(A,B).

The exact normalized log identity is

    log beta_n = w(1-r) e_n / B^19.

Let g=gcd(e_3,e_6,e_10,e_15,e_21). Since e_21=P_21 is congruent to A^19 modulo B and gcd(A,B)=1, gcd(g,B)=1. Therefore g divides both P_3=A+2B and P_6. Substitution A=-2B gives P_6(-2B,B)=9B^4, so g divides9. In particular

    k_n=e_n/g are positive integers with gcd_n k_n=1,
    k_21>=20 B^19/9.

Set t=exp(w(1-r)g/B^19)>1. Then beta_n=t^k_n. Bezout integers z_n with sum z_n k_n=1 give t=product beta_n^z_n. Thus t is an algebraic number in the SAME bounded-degree field, not a root extension of unbounded degree. Its height satisfies

    h(beta_21)=k_21 h(t).

This gcd/Bezout step is essential. Merely taking a B^19-th root of an algebraic beta would not supply a bounded-degree height gap.

## 5. An elementary effective positive-height gap

For any real algebraic t>1 of degree d<=D,

    h(t)>1/[D*2^(D+2)].                           (G)

For completeness, write its primitive integer minimal polynomial as P(X)=a product_(j=1)^d(X-t_j), with t_1=t and a>0. It has P(1)!=0, so

    1<=|P(1)|
      <=2^(d-1)(t-1) exp(d h(t)).

Also t<=exp(d h(t)). If h(t)<=1/[D*2^(D+2)], put x=d h(t)<=2^(-D-2). The elementary inequalities exp(x)<=2 and exp(x)-1<=2x then give the right side at most 2^(D+1)*2^(-D-2)=1/2, contradiction. This deliberately crude bound does not use Lehmer, Dobrowolski, Schanuel or any ineffective theorem.

Combining (U), (G) and Section4 gives

    20 B^19/[9D*2^(D+2)] < C0+C1 log B
                               <=(C0+C1)B.

Thus every denominator obeys

    20 B^18 < 9D*2^(D+2)*(C0+C1).                 (B)

Take any integer Bmax with 20 Bmax^18 >= 9D*2^(D+2)*(C0+C1). Then B<Bmax. Integer arithmetic computes such a bound. Its size and computational cost may be enormous; neither a feasible runtime nor an executed value is asserted.

## 6. Finite exact census and relation to the original bottleneck

Enumerate coprime 0<A<B<Bmax. For each rational r=A/B, compute its finite algebraic strict critical locus using the inherited polynomial system. Enumerate every multiset of at most N pairs. Divide its algebraic factor product from m and test the pure drift-plus-rational-residue equations. As in the accepted singleton arithmetic note, w=log(beta_3)/(3-R_3(r)); a=-log(quotient_m_1)-w. Positivity and all equalities reduce, after rational denominator clearing, to comparisons of positive algebraic power products. Hence each test terminates without a real-exponential feasibility oracle. Retain precisely the successful presentations.

The old Baker/projective plus all-r critical-finiteness theorem says every ALGEBRAIC residue in a critical presentation of algebraic m is rational. Thus the finite census covers all algebraic-residue critical presentations with at most N factors, not only a supplied rational node.

For inputs outside the now-classified endpoint envelopes, the accepted effective endpoint-exclusion theorem supplies an interior residue interval and a retained-count bound from the algebraic full singleton. That bound may be used as N here. Equivalently, a supplied compact rational residue interval and the uniform critical loss floor supply N. These are necessary critical-presentation bounds and are not arbitrary witness-size bounds.

This closes the unknown RATIONAL residue enumeration step on that critical branch. It still does not decide whether one of the enumerated presentations admits a different finite positive realization. Transcendental residues and transcendental retained factors remain possible in the unresolved arithmetic branch. Hidden tuple extraction from a positive-dimensional original joint fibre, tied/exposed or INDEPENDENT slots, and all-core completeness are unchanged. No implication from a nonempty list to original NO is made.

## 7. Prior and evidence

- Old source-specific polynomial and Baker provider: ALL-RESIDUE-CRITICAL-FINITENESS.md, https://github.com/Sodelin/Research-Commons/blob/9e0ec4fce82cbe699b9236116beb6e6046f9901c/research/2026-10-02-codex-g3-parametric-critical-0330z/ALL-RESIDUE-CRITICAL-FINITENESS.md . Exact local readback is ../g3-astra-continuous-20261006-0732z/providers/ALL-RESIDUE-CRITICAL-FINITENESS.md; its final old review and reduced B coefficient JSON are preserved alongside.
- Classical height definition, power behavior and bounded degree/height background: Joseph H. Silverman, Arithmetic Dynamics, Arizona Winter School2010 notes, Section4.1, https://swc-math.github.io/aws/2010/2010SilvermanNotes.pdf . The primary text was read directly. The bounds actually needed above are derived explicitly; Northcott finiteness is not being invoked as an unexplained effective constant.
- Input-effective critical count and endpoint exclusion, newly accepted earlier in this trial: UNIFORM-CRITICAL-PURITY.md, EFFECTIVE-ENDPOINT-EXCLUSION.md, and the independently executed K1 endpoint-emptiness/source corollary, all at their stated source-component hypotheses.

A search of the recovered G3 notes and full-scope index found no existing rational-residue height bound. This limited prior check is not a historical novelty claim. No symbolic computation has been run for this note at freezing time.
