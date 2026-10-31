# Conditional application on an actual serial diagonal fibre

31 October 2026. dot. Hand deduction; no new source or numerical computation. Use only the natural projective opaque-root serial class and one fixed reference of PROOF.md, not arbitrary admitted networks.

Suppose a whole actual physical serial word has fixed strictly positive diagonal entries D_r*. Every ordinary gap and RAW cell has diagonal in(0,1]. Scalar root-block diagonals multiply. For each atom and every chronological prefix P (including points inside ordinary gaps),

    d_r(atom)>=D_r*,     D_r(prefix)>=D_r*.

This is immediate because the product of all other physical factors is at most1. In particular reciprocal d8,d10 are bounded by target diagonal reciprocals, without a q>=q0 premise or any coin margin. The preceding q>=q0 estimate is a convenient bound for independent individual sources, not necessary when this exact fibre premise is actually supplied.

Prefix ratios satisfy

    D12* <= a=D12(prefix)/D10(prefix) <=1/D10*,
    D10* <= b=D10(prefix)/D8(prefix) <=1/D8*,
    (D10*)² <= theta=D10(prefix)²/[D12(prefix)D8(prefix)]
                                    <=1/(D12* D8*).

Every physical prefix is stochastic on the fixed complete forest carrier, so its entries and norm are bounded independently of word length. Bounded V,W consequently bound the framed prefix G_P=W P V. After right-diagonal normalization its12-to10 block is bounded by a target-dependent constant. The accepted shape reduction and chronological product identity identify that block as Qprefix*A. Taking the selected entry gives

    |Qprefix| <= C(D10*)/|U[0,2]| <= C'(D10*) h^(-m_U12).

This is a word-count-independent polynomial bound on the signed accumulated profile, not a bound on total variation or on sum_i |alpha_i|. Arbitrarily many positive and negative increments can cancel while the path stays bounded; summing a pointwise residual estimate over atoms may still incur a word-count loss.

These constants depend on the fixed positive target diagonal values. A moving reference/target family needs separate uniform lower bounds on D_r*; no such bound is inferred merely from writing D_r*=s_r(h)^N with variable N. The statements do not make a general G4 rival an isolated serial word or identify its latent diagonals from an incomplete observation panel. Any full-source use still needs the exact finite-I semantic adapter.

Hence the useful distinction: exact fibre constraints can remove rare-coin/diagonal denominator problems at this fixed carrier, but they do not resolve reference normalization loss, direct local residual accumulation, or full-fibre signed domination. No master closure follows.

## Additional positivity-budget bound (separate from bounded-profile reasoning)

There IS an independent coarse total-variation estimate using actual stochastic positivity. Let L=-log D12*. For each physical source atom K_i, projectivity of its no-merger event gives d_r(K_i)>=d12(K_i) for all root counts r<=12. Each stochastic row of K_i has diagonal d_r, hence in the induced maximum-row-sum norm

    ||K_i-I||_infinity = max_rows 2(1-d_r(K_i))
                       <=2(1-d12(K_i)).

(The identity entry is its unchanged forest; all other entries are nonnegative.) Also

    sum_cells(1-d12(K_i)) <=sum_cells -log d12(K_i)<=L.

The second inequality retains ordinary gaps in the total product D12*; they contribute additional nonnegative cost. In particular total ordinary duration is at most L/lambda12. Since G_i-I=W(K_i-I)V and V,W are bounded, every offdiagonal framed entry is bounded by C(1-d12(K_i)). Combining with the previous atom/prefix diagonal bounds gives

    sum_cells |alpha_i| <= C(D*) L/|U[0,2]|,
    sum_cells |beta_i| <= C(D*) L/|U[2,13]|,
    sum_cells |lambda(Z_i)| <= C(D*) ||lambda|| L.

Here alpha,beta,Z are exactly the accepted RAW chronological interaction-picture source quantities; the bounded prefix factors a,b,ab are absorbed into C(D*). Continuous ordinary profile variation is also bounded by C(D*)L. Thus total scalar-profile variation has a polynomial reference bound independent of word count, using the extra positivity-budget argument rather than boundedness of Q alone. For example sum alpha_i² <=(sum |alpha_i|)². These estimates bound the entire scalar residual crudely, with reference inverse powers and target cost constants.

This is a classical stochastic mass-budget estimate at the exact source use-site, not a newly discovered contraction theorem. It does not supply favourable epsilon powers or dominance by the SAME Energy: the accumulated target budget L can stay fixed while dust atoms become individually small. Nor does it identify a sharp local residual cancellation. Any hoped-for stronger use must keep reference losses, exact physical scaling, source coefficients, and the full endpoint equations. No arbitrary signed kernels, independent I/C fits, or extra source selector were used.

## Explicit constants and a coarse full scalar-residual bound

Write u=D12*, v=D10*, w=D8*, L=-log u, and let

    K0=sup_(0<=h<=h0) ||W(h)||_infinity ||V(h)||_infinity < infinity,
    A0=U[0,2], B0=U[2,13],
    Theta=1/(u w),
    Ca=2K0/(v² |A0|),
    Cb=2K0/(w² |B0|),
    Cz=2K0 ||lambda||_1/(v w²).

Here ||lambda||_1 is the sum of absolute coefficients in the fixed eight-coordinate row, so |lambda(X)|<=||lambda||_1 max_j|X_j|. A0,B0 are selected orbit-aggregated entries, not the target-diagonal symbols u,v,w. The interval excludes their zeros as in PROOF.md. No positivity of A0 or B0 is assumed.

For delta_i=1-d12(K_i), the RAW conventions give exactly

    alpha_i=a_i G_i[0,2]/(d10(K_i) A0),
    beta_i=b_i G_i[2,13]/(d8(K_i) B0),
    lambda(Z_i)=a_i b_i lambda(G_i12,8)/d8(K_i).

Using a_i<=1/v, b_i<=1/w, d10(K_i)>=v and d8(K_i)>=w proves

    |alpha_i|<=Ca delta_i,
    |beta_i|<=Cb delta_i,
    |lambda(Z_i)|<=Cz delta_i.

Thus their sums are at most Ca L, Cb L, Cz L respectively. Along ordinary gaps Q'=a<=1/v and total duration<=L/66, hence

    TV(Q)<=L(Ca+1/(66v)),    sup|Q|<=TV(Q).

This total variation includes both ordinary intervals and all source jumps, with Q starting at zero. It uses the actual shape reduction identifying all these entries in the SAME fixed frame; one cannot independently choose scalar increments.

For the retained full source residual

    R=sum_i [(beta_i-theta_i alpha_i) Q_i^-
                    +lambda(Z_i)-theta_i alpha_i²/2],

we have theta_i<=Theta and sum alpha_i²<=(Ca L)². Therefore the explicit word-count-independent estimate is

    |R| <= L² (Cb+Theta Ca)(Ca+1/(66v))
                      +Cz L + (Theta/2) Ca² L².

No endpoint equations were needed for this absolute bound. On an endpoint where the accepted identity says Energy=R, it supplies an upper bound on Energy, NOT a strict inequality against Energy or equality classification. The constants remain functions of h through A0,B0,lambda and can blow up polynomially. If u,v,w vary with h or with a target family, their inverse factors must also be retained.

In particular there is no hidden assumption of a uniform word length, coin margin, bounded number of source jumps, or extra COMMON budget. The exact joint serial diagonal-factorization premise and the fixed positive target diagonals are essential. This calculation is not a substitute for showing that a finite legal I panel forces those premises for every original G4 rival.

## Separate paired-COMMON-clock corollary

Source-use observation supplied by the G3 research context; not an added premise of original G4. Suppose the actual equal-arm serial word is independently known to have COMMON pair exposure H: the product of its ordinary survivals and its equal-arm cell survivals q_i is exp(-H). In COMMON mode a cell routes all relevant roots together, so its no-merger diagonal is q_i^lambda_r; ordinary factors have the same expression. The RAW independent diagonal lower bound d_r(q_i,g_i)>=q_i^lambda_r therefore gives for the whole physical word

    D_r >= exp(-lambda_r H).

This does not require I diagonals to be exactly prescribed. Each atom/prefix diagonal is again at least the whole diagonal, so all preceding estimates apply with LOWER bounds

    u=exp(-66H), v=exp(-45H), w=exp(-28H), L=66H.

Replacing the exact budget -log D12 by its upper bound66H preserves the displayed inequalities. It yields reference-polynomial, word-count-independent constants controlled by this actual COMMON clock, with no coin margin. It still supplies no positive power of microscopic dust size and no signed domination.

This premise belongs to the actual paired-COMMON-clock use-site. A natural-I panel may not query COMMON coordinates merely to make the argument work. Neither same-target membership nor a COMMON budget is furnished for an arbitrary G4 rival by this corollary. Unequal-arm or nonserial sources require their own supplier and are not silently included.
