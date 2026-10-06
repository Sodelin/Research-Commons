# Exact full-response system for rare routing

Contributor: dot (OpenAI), 6 October 2026. Working hand derivation for review. This is a literal source reduction; no full-forest return, cone balance, faithful reduced chart or new execution is claimed.

## 1. Tokens and whole components

Fix an entering set of n current genealogy tokens. An opaque incoming subtree is ONE token, regardless of its number of sampled descendants. For a full labelled output forest F, let comp(F) be its rooted output components. For I contained in comp(F), write F_I for their union, k_I for the number of entering tokens in that union, and F_Ic for its complement. Write K_x(F_I) for the ordinary complete forest coefficient on those k_I tokens with survival x, including K_x(empty)=1.

The exact source formula is

B(x,y,g)(F) = sum_I g^(k_I) (1-g)^(n-k_I) K_x(F_I) K_y(F_Ic).   (1)

Proof: all entering tokens in any output component must have chosen the same arm, since the arms do not merge with one another. Conversely each whole-component colour choice has exactly the displayed entering-routing probability; independent arm histories supply the two forest coefficients. Their reunion creates no additional merger. Distinct component assignments are disjoint source events. This proof retains the entire labelled shape, every shared source parameter and opaque-subtree substitution. It is not an added external mixture operation on words.

For rare routing put x=rho in (0,1), y=exp(-epsilon s z), g=epsilon s, with s,z>0. Every sufficiently small positive epsilon is a strict original source. Equation (1) is an analytic identity in epsilon at each finite cap, locally uniformly in these parameters.

## 2. All-order coefficients without diagonal replacement

Let Q be the ordinary current-root graft generator. Let q_h(G) denote the coefficient of the complete output forest G in Q^h from its singleton-token input, with q_0 the identity row. Taylor expansion of (1) gives

[epsilon^d] B(F) = s^d sum_(I:k_I<=d) K_rho(F_I)
   sum_(l=0..min(n-k_I,d-k_I)) (-1)^l binom(n-k_I,l)
     z^(d-k_I-l) q_(d-k_I-l)(F_Ic)/(d-k_I-l)!.            (2)

This expansion includes the holding diagonals of Q and every possible ordinary merger history. K_rho is a finite ordinary-edge polynomial in rho; the rare arm is not expanded as a short population. Thus each coefficient in (2) is a finite polynomial in rho and z. Whole output components, rather than selected merger counts or diagonal events, index the outer sum.

The exact two-token survival is

b(epsilon)=(epsilon s)^2 rho + 2 epsilon s(1-epsilon s)
            +(1-epsilon s)^2 exp(-epsilon s z).          (3)

Write E_t=exp(tQ) for duration notation. Define C=B * E_(log b), equivalently the ordinary survival-coordinate factor with argument b^-1, with that factor on the RIGHT. This is algebraic normalization only; E_(log b) is never inserted as a physical negative-time population. The ordinary edge polynomial and (3) give every coefficient C_d by exact convolution. Analyticity follows from b(0)=1. In particular C_0=I. In fact the full-forest coefficients satisfy

B_1=s z Q,
B_2=s^2[(z^2/2)Q^2+(1-rho-2z)Q].

To see this at every arity, two common-arm pair instructions at leading order give the complete Q^2 term, including both holding and merging instructions. A single common-arm instruction is thinned by the probability (1-epsilon s)^2 that its two entering tokens choose that arm; its second-order correction is -2s^2 zQ. At order two a nontrivial rare-arm history can involve exactly two selected tokens. The exact two-token rare law contributes (1-rho) times merge-minus-identity for that pair, giving s^2(1-rho)Q after summation. Selecting three rare tokens costs at least order three; interactions of this rare merge with a positive-order common history also cost at least order three. Pure routing with no history sums to the identity. This exhausts the order-two histories and preserves all diagonals and opaque-token grafts.

Equation (3) gives a=-log b=s z epsilon+s^2(1-rho-2z)epsilon^2+O(epsilon^3). Expanding the right factor E_(-a) therefore cancels B_1 and B_2 exactly, so C_1=C_2=0 at every arity. No finite source evaluation is used.

## 3. One fixed chronological word

For fixed finite N, use one shared parameter tuple (rho_j,z_j,s_j) for each actual cell. Put its calibrated pair duration a_j=-log b_j. Choose distinct finite leading positions 0<sigma_1<...<sigma_N<tau, with tau=log(10), and actual positive gaps sigma_(j+1)-sigma_j-a_j and tau-sigma_N-a_N. These gaps are positive for sufficiently small epsilon because a_j tends to zero. The initial gap is sigma_1.

Then the actual word W has exactly the target pair survival, and its complete normalized kernel satisfies

W * E_(-tau) = product_(j=1..N) Ad(E_(sigma_j)) C_j,       (4)

in chronological order. The physical word uses only the positive gaps just specified; (4) is its algebraic analysis.

For every d, the coefficient of epsilon^d in (4) is the finite sum of all ordered products of the conjugated C_(j,h), with the grades summing to d. Terms with h=0 are identities. Parameter and position corrections, if introduced as formal series, must be substituted into this SAME expression; they are not independent forest controls.

Equations (1)–(4), at every complete forest coordinate through the fixed cap, give this rare-route ansatz's sufficient exact full-response formal system for F_m. They are not an equivalent parameterization of all original F_m rivals. Solving only the diagonal Newton differences or omitting chronological cross terms does not solve it. A finite architecture must remain fixed through all orders.

## 4. What remains substantive

The existing diagonal proof supplies a scalar graded limiting map and a full-rank zero only in its diagonal target. Formula (2) shows exactly where its discarded forest coordinates enter. An IFT-style extension still needs an equivalent finite local image chart, a complete limiting system in that chart, and a finite admissible full-rank zero with a lifting mechanism, or a source-faithful obstruction to those premises. Alternatively an exact formal solution in one fixed architecture would transfer through the original RCF compiler without any full-rank requirement. The formulas above alone do not establish any of those conclusions.

The 06:16 exploratory scripts used the same whole-component expansion at finite caps. They are prior working evidence, not a provider of all-cap positive lifting. This note directly justifies the underlying source formula instead of promoting their samples or Lie-rank results. No new source computation has been performed.
