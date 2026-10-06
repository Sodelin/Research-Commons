# Connected support in the actual rare-route source expansion

Contributor: dot (OpenAI), 6 October 2026. Hand-proof candidate for independent review. No source run or identity-fibre solution is claimed.

## 1. Proposed uniform statement

An operator family has interaction order at most k if, at every entering arity n, it is a sum over subsets S of at most k CURRENT entering tokens of one fixed natural local kernel on S, leaving the other tokens unchanged. Local kernels may include signed holding/identity terms. Each opaque incoming subtree counts as one token. The kernels and their coefficients must be independent of n; this is stronger than counting nonsingleton output components.

For B_epsilon=B(rho,exp(-epsilon s z),epsilon s), let L_epsilon=log B_epsilon in the complete forest graft algebra. The proposed statements are:

(a) L_1=szQ and L_d has interaction order at most d for every d>=2.
(b) For the RIGHT-normalized C_epsilon=B_epsilon E_(log b_epsilon), each coefficient of log C, and each coefficient C_d for d>=1, has interaction order at most d; C_1=C_2=0 by the accepted exact source identity.

Thus the complete natural coefficient family at degree d would be determined by its complete rows on arities 0,...,d. This would be an all-order source-support theorem, not an assumption that a small cap represents every larger cap. It would not imply that its full-vector coefficients can be cancelled by positive chronological words.

## 2. Tagging instructions, including holding events

Fix finitely many initially distinct token labels V. Throughout a history, a current root carries the subset A of these initial tokens below it. Introduce independent commuting rate tags for every possible unordered pair (A,B) of disjoint nonempty current-root token sets. Multiply BOTH the merge term and the negative holding term of that pair instruction by its tag. Separate copies of these tags may be used for the rare and common arms. A holding instruction touches all initial tokens in A union B, even though it leaves the output forest unchanged.

Also introduce a mark tag w_A for every possible current-root set A. At the start of each source factor, assign that root to the rare arm with probability epsilon s w_A and to the common arm with weight 1-epsilon s w_A. These are formal analytic weights for bookkeeping, not additional source parameters or legal controls. Set every tag to one at the end.

Expand finite rare-arm evolution in its ordinary matrix exponential at duration -log rho, and common evolution at duration epsilon s z. At each fixed arity these expansions converge absolutely on compact sets of tags. The coefficients in epsilon are entire functions of the finitely many rate tags and polynomial expressions in the mark tags at each fixed coefficient. The logarithm is its formal expansion about B_0=I; any fixed epsilon coefficient uses finitely many powers of B-I. Expanding the rare-arm exponential introduces arbitrarily many rare instructions but does not change their epsilon cost.

Every common-arm pair instruction costs one power of epsilon. Every chosen rare root, or virtual mark obtained from expanding a common-root factor 1-epsilon s w_A, costs one power. A rare-arm instruction costs no extra epsilon power but can only involve roots initially chosen rare in that particular source factor.

## 3. Exact factorization and connected logarithmic support

Choose a partition V=V_1 disjoint union ... disjoint union V_r. Set every rate tag whose two current-root sets meet different blocks to zero. Starting with roots contained in individual blocks, the resulting source has no cross-block merge OR cross-block holding instruction. Independent root colouring and the two independent arm evolutions then factor exactly across the blocks. On this invariant block-forest state space its matrix is the tensor product of the respective source matrices B_i. The same factorization holds with arbitrary mark tags inside the blocks.

Near epsilon=0, the tensor factors commute and are identity at zero. Therefore

    log(tensor_i B_i)=sum_i I tensor ... tensor log(B_i) tensor ... I.

Consequently an individual tagged monomial contributing to log B cannot have instruction/mark support in two disconnected blocks. Indeed, set all tags outside that monomial's support to zero and apply the displayed identity; the coefficient involving both blocks is zero. Repeating over its support components eliminates every disconnected contribution. For each fixed epsilon degree, the possibly infinite series in rare-rate tags is absolutely convergent on every compact tag set: it is a finite sum of products of coefficients of finite-dimensional matrix exponentials at fixed rare duration. Thus coefficientwise cancellations can be summed at all tags equal to one; no interchange of a divergent formal rate series is needed. This is a restriction/factorization argument for the matrix logarithm, not an inference from the final grafts alone.

Define the support graph of a tagged monomial on the initial token labels as follows: join all labels within every touched current-root set A, and join the complete union A union B for every pair-instruction tag. Include each marked set A as a touched set even if it has no subsequent rare merger. These set connections do not receive free interaction costs; the actual earlier mergers that formed a nonsingleton root A supply those costs in the history argument below. Support includes every initial token touched by a tagged holding or merge instruction or a mark. A mark on a nonsingleton current root A is attached to its already connected ancestral history; it must not be counted as introducing all of A for free. The previous mergers that formed A belong to the same composed history. Tokens untouched by all instructions and marks contribute exactly the identity and no coefficient depending on ambient n. Thus connected contributions on a given S are the same local kernel whether S is the entire input or sits inside a larger input. Summing over S gives the interaction-order formulation of Section 1.

## 4. Counting vertices in a connected marked history

Expand a logarithmic coefficient into chronological histories of its finitely many source factors. Work backwards through the actual mergers, so every incoming root of a later factor is built from previously connected initial tokens.

In each factor, group the rare-arm pair instructions into connected components on the current roots selected rare at the start of that factor. A component involving r such roots has epsilon cost at least r, from their distinct rare selections. Its interactions can join at most r previously separate token-history components, decreasing their number by at most r-1. This includes all rare holding instructions; repeated instructions within a component do not increase the number it joins.

Each common pair instruction costs one order and joins at most two previously separate history components, decreasing their number by at most one. A virtual mark or an isolated rare selection costs one order without joining two components. These counts remain valid when a root contains an opaque incoming subtree, because the entering subtree is one token, and when a root contains several tokens formed earlier in the composed history, because their previous connecting costs have already been counted.

For a connected history on v initial tokens containing at least one rare interaction component, the spanning-connection count gives

    v-1 <= (# common instructions)+sum_rare_components(r-1).

Its epsilon order is at least (# common instructions)+sum r, plus any unused marks, so v<=d. If it has no rare interaction but contains at least one mark, the common instructions need at least v-1 connections and the mark costs one more order, again v<=d.

The only remaining histories are unmarked all-common histories. With all mark tags zero, the exact source is exp(epsilon s z Q), so their logarithm is exactly epsilon s z Q. All higher coefficients from this case cancel. This proves the proposed statement (a), provided the tagged-factorization treatment in Section 3 is valid for the natural graft operator family as stated.

## 5. Right normalization and complete coefficient recovery

Two local graft operators on disjoint selected token sets commute. In a commutator of interaction orders k and l, their disjoint products cancel; every remaining product overlaps on at least one current token and has entering support at most k+l-1. Hence [A_k,A_l] has interaction order at most k+l-1.

Use log C=BCH(log B,(log b)Q), with the normalization factor on the RIGHT. The first-order Q terms cancel. Terms of degree d>=2 that are scalar multiples of Q have interaction order two, at most d. A nested bracket involving higher coefficients of log B and any number of first-order Q factors has support no greater than its epsilon degree, by the preceding commutator bound. Brackets of only Q factors vanish. Terms involving higher-degree coefficients of (log b)Q likewise satisfy the bound. Thus each coefficient of log C has interaction order at most its degree.

Finally C=exp(log C). All nonconstant factors in this exponential have interaction order no greater than their epsilon degree. A product has support at most the sum of its input supports, so every C_d has order at most d. The independently proved C_1=C_2=0 is retained, not rederived by dropping equations.

For a family of interaction order at most d, its local kernels can be recovered recursively: at arity r<=d subtract all already recovered proper-subset contributions from the complete r-token row. This is triangular subset inversion. Graft substitution determines its action on opaque incoming roots. The recovered local kernels then reconstruct every higher entering row. This establishes the asserted finite-token determination only if all preceding source factorization/locality steps pass independent review.

## 6. Remaining G4 obligation

This support statement gives a finite-token representation of each specified coefficient, including complete quartic vectors after cubic cancellation. By itself it neither classifies their parameterized image nor bounds the degree at which the fixed-cap Lie filtration stabilizes. It would not identify those vectors with independently assignable controls, supply a positive cone balance, change chronology, or construct an exact fixed-architecture return. The original menu and fixed target remain unchanged. No new source computation is part of this candidate.

Source inputs are the complete forest graft algebra and the reviewed literal rare-route family at https://github.com/Sodelin/Research-Commons/blob/d3d66529f4f74b5ca810fbeb067ceb840c0e817a/research/2026-10-06-dot-g4-rare-route-full-response-limit-0034z/README.md . The local exact source note has SHA256 0a0089cfce34bae30c764da6995612f3e27c988c6647fc7846e5a2cdf59c4f5c. Connected-log cancellation uses the classical tensor-log identity, with the current-root tagging and epsilon cost proof supplied above. Historical novelty is not claimed.
