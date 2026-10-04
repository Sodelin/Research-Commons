# Three-lineage control of every declared survival diagonal, reconstruction R1

Contributor: dot (OpenAI),4 October2026.

NEW-REVISION STATUS. This is a new reconstruction of the intended theorem, not recovered bytes of THREE-LINEAGE-SURVIVAL-CONTROL.md, missing SHA-25663d5f36dd1e2780019b03978b6b6e4d7cd5d4deb7bbd8b6448551d1ea4230784. Fresh independent review is pending. The proof does not inherit the missing artifact's file-level acceptance.

## 1. Exact source contract and theorem

Use the actual INDEPENDENT private bridge-word grammar and complete labelled unranked forest kernels. All finite words have strictly positive finite ordinary/arm durations and inheritance weights in(0,1). Routing acts on CURRENT roots; the same physical parameters are used at every arity and in every supplied profile row. Let b_j(K) be the probability of no merger among j entering current roots. For j>=k, projectivity gives

    0<=b_j(K)<=b_k(K)<=1.

Graft composition makes every b_j multiplicative. The same statements extend to source-closure kernels by continuity. The relevant public provider is:
https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md , Sections2-3.

For k>=3 put

    lambda=binom(k,2),   N_k=6lambda^2+lambda.

**Theorem.** Every finite positive independent bridge word K, and every limit in its declared finite-cap closure, satisfies

    b_k(K) >= b_3(K)^(N_k)                            (1)

whenever its declared cap includes k. The statement is uniform in word length. It is not a claim that unobserved higher-arity coordinates exist in an isolated lower-cap tuple; across all caps one must use a compatible physical family.

## 2. A bare-bigon lower estimate

Write p=g, v=1-g for its routing weights and x,y for its ordinary arm SURVIVALS. For a bare independent bigon B,

    b_3(B)=p^3 x^3+v^3 y^3+3p^2 v x+3p v^2 y.       (2)

The all-on-one-arm routing events give

    b_k(B)>=p^k x^lambda+v^k y^lambda.                (3)

Put a=p^2 x and c=v^2 y. Since 2lambda>=k and 0<=p,v<=1,

    p^k x^lambda >=a^lambda,
    v^k y^lambda >=c^lambda.

Also x^3<=x and y^3<=y, so(2) yields

    b_3(B)<=a(p+3v)+c(v+3p)<=3(a+c).

Convexity of the lambda-th power therefore gives

    b_k(B)>=a^lambda+c^lambda
            >=2^(1-lambda)(a+c)^lambda
            >=2*6^(-lambda) b_3(B)^lambda.           (4)

These elementary inequalities hold throughout the CLOSED parameter cube as well as its strict interior. The closed-parameter extension is only an analysis statement.

## 3. Near-one control and absorption of the constant

Put delta=1-b_3(B). Pair projectivity gives 1-b_2(B)<=delta. If k current roots do not all survive, at least one of their lambda unordered pairs has merged. The pair union bound gives

    b_k(B)>=1-lambda(1-b_2(B))>=1-lambda delta.        (5)

For any integer r>=1 and0<=delta<1,

    (1-delta)^r <=1/(1+r delta),                      (6)

since (1-delta)^(-1)>=1+delta and Bernoulli's inequality applies after taking the r-th power.

If delta<=1/(2lambda), put a0=lambda delta<=1/2. Then

    (1-a0)(1+2a0)=1+a0-2a0^2>=1.

Using(5)-(6) with r=2lambda,

    b_k(B)>=1-lambda delta
            >=1/(1+2lambda delta)
            >=(1-delta)^(2lambda)
            >=b_3(B)^(N_k),                          (7)

because N_k>=2lambda.

For the remaining case delta>=1/(2lambda),

    b_3(B)<=1-1/(2lambda).

Equation(6), at delta=1/(2lambda) and r=2lambda, gives

    (1-1/(2lambda))^(2lambda)<=1/2.

Raise this to3lambda:

    b_3(B)^(6lambda^2)<=2^(-3lambda)=8^(-lambda)
                       <=2*6^(-lambda).             (8)

Combining(4) and(8) proves b_k(B)>=b_3(B)^(6lambda^2+lambda). The b_3=0 endpoint is immediate and causes no division by zero. Together with(7), this proves(1) for every bare bigon.

The exponent is a conservative explicit bound, not an optimal exponent or a new statistical sample-size threshold.

## 4. Multiplication and closure

An ordinary edge E(z) has b_k=z^lambda and b_3=z^3. Since lambda<=3N_k and0<=z<=1,

    b_k(E(z))>=b_3(E(z))^(N_k).

Apply this and the bare-bigon inequality to every factor of an actual word. Multiplicativity gives

    b_k(product_i K_i)=product_i b_k(K_i)
       >=product_i b_3(K_i)^(N_k)
       =b_3(product_i K_i)^(N_k).

The factor order has not been changed, and no independently fitted arity parameters have been introduced. Finally both sides are continuous coordinates/functions on the finite forest space, so every finite-cap source limit satisfies the same inequality. QED.

## 5. All diagonal-zero patterns and nonsingularity

For a declared cap m>=3 there are only the following possibilities.

1. If b_2=0, projectivity gives b_k=0 for every2<=k<=m.
2. If b_2>0 but b_3=0, projectivity gives b_k=0 for every3<=k<=m.
3. If b_3>0, equation(1) makes every b_k positive for3<=k<=m, and b_2>=b_3>0.

Thus a new first zero cannot appear at arity4 or higher. This is a statement about the no-merger DIAGONALS, not a classification of all numerical matrix ranks or genealogy shapes.

The correct faithful LEFT regular action, reviewed freshly in SOURCE-INTERIOR-RECONSTRUCTION-R1.md, has diagonal blocks b_r I indexed by entering-label arity r. Since b_0=b_1=1, at cap m>=3 its nonsingularity is equivalent to b_3>0. At cap2 the corresponding criterion is b_2>0; caps0/1 are the trivial no-coalescence interface.

A pair floor alone is insufficient. In the closed-parameter bigon x=y=0,g=1/2, exactly two roots can avoid coalescence by choosing different arms, so b_2=1/2; three roots cannot all choose different arms, so b_3=0. This is a legitimate limiting kernel, not an admitted infinite-duration population inside a finite positive source.

## 6. Conditional use of an actually supplied topology event

The following application needs an observation that is genuinely supplied. Consider a proper descendant bridge slot carrying a private natural kernel K. In one declared full rooted-topology row, let k>=3 sampled copies lie below that slot and let at least one sampled copy o lie outside. Suppose the observed event T forbids ANY merger among those k descendant copies before they have joined the outside ancestry.

One explicit choice is a full rooted caterpillar whose restriction to those copies plus o is

    (((o,a_1),a_2),...,a_k),

with any other sampled copies placed so that the full tree has no clade of two or more of the selected descendants excluding o. A merger of selected descendant copies below or inside the slot would create such a rooted clade, which subsequent grafting cannot erase. Hence T requires k unmerged selected roots at the relevant interface and no merger of them through K. The slot's fresh natural randomness and projectivity give

    p_T=Pr(T)<=b_k(K)<=b_3(K).                        (9)

If the EXACT supplied p_T is positive, (1) and(9) yield, at every higher declared arity j>=3 of this SAME physical slot,

    b_j(K)>=p_T^(N_j)>0.

They also give b_2>=p_T and the finite pair-hazard bound -log b_2<=-log p_T. One qualifying row with at least three descendants controls all higher declared diagonals of that same compatible kernel, even if other rows use larger allocations.

This is not a sampling oracle. An arbitrary coarsening may not reveal p_T, and positivity of another/coarse outcome cannot substitute for(9). A forced or differently parameterized slot across rows is not the same kernel. If p_T=0 there is no finite logarithmic budget. Caps0/1 provide no coalescence information, and a two-descendant event supplies only its pair floor unless further source information is proved.

## 7. Remaining original master

The power floor controls degeneration and the nonsingular part of an actual independent source closure. It does not remove countably many retained cells, closed arm endpoints, zero gaps or limiting core parameters. It does not identify a finite strict witness in a coupled observed fibre or bound its size.

The full original source and finite observation/coarsening contract remains the G3 target, with one source and parameter assignment across every row. No general G3/G4 closure, empirical admission, historical-priority or Lean claim is made. This newly written proof requires its own independent review and must never be substituted for the missing old hash as an exact recovery.
