# A cap-dependent marked G3 bound effectivizes finite forcing

Contributor: Codex role 5, 8 October 2026. HAND CANDIDATE for independent review. Original G3/G4 remain OPEN. No compiler, CI dispatch, solver, parameter scan, or source modification was performed.

This companion strengthens the effective bridge in [algebraic-profile coverage](ALGEBRAIC-PROFILE-COVERAGE-AND-STOPPING.md). It distinguishes two uses of a witness bound:

- To **prove mathematical finite forcing from compression alone**, positive-stopping0846 Claim D needs one inequivalent representative bound uniform in the prefix cap.
- To **compute a certificate when finite forcing is independently true**, a total marked witness bound may depend on that cap.

The second statement does not contradict the first. No cap-dependent bound is asserted to make a non-forcing target forcing.

## 1. Actual source and finite algebraic query

First work in the inherited natural strict private INDEPENDENT two-port class

    E(z0) B(x1,y1,g1) E(z1) ... B(xj,yj,gj) E(zj).

One finite positive graph word and one natural tuple supply every complete labelled forest coordinate. Original passive full rooted-topology completions are retained, with no exposed private cell controls, no boundary-crossing shared register, no zero duration or endpoint inheritance. Root genealogies remain indivisible tokens.

Let U be a supplied strictly positive algebraic candidate of normalized length L. Let Gamma_(j,m)(theta) be the full original capped forest tuple for shape j. It is a finite rational polynomial tuple effectively supplied by the source compiler. Denote by R_(U,j)(theta) the all-copy equality relation to U:

    j != L: R_(U,j) is FALSE;
    j == L: ordered connector equality and, at every cell,
            equality to U's triple OR its arm exchange.

This relation is supplied by the accepted passive normal form. Its complement is a finite Boolean polynomial formula with algebraic coefficients. It is a mathematical source constraint, not a new observation or a count flag. Every branch keeps the same original physical tuple across response rows.

Define

    E(U,m,j) := exists theta in the strict shape-j domain:
                 Gamma_(j,m)(theta)=Gamma_(L,m)(U)
                 AND NOT R_(U,j)(theta).                (1)

For each supplied j, (1) is an effectively decidable RCF sentence. The arbitrary-size bad-prefix question is

    Bad(U,m) := exists j>=0 E(U,m,j).                    (2)

By full-topology tomography and the normal form, this is exactly the presence of at least one admitted prefix-matching source differing from U at some later original legal experiment. It does not fit diagonal-only constraints.

## 2. Input-dependent exclusion-preserving G3 compression

The additional source premise is a **total computable** function R(U,m) such that

    Bad(U,m) implies there exists j<=R(U,m) with E(U,m,j). (3)

R(U,m) may grow with m. It bounds one source outside U's equality orbit, not every source in the prefix fibre. It is an exclusion-preserving G3 witness bound for the finite source-local query (1); it is not supplied by ordinary G3 membership, whose witness can be U itself. The hypothesis quantifies over every finite algebraic candidate U and every finite cap m in the stated source class.

**Lemma D.** In this finite encoding, (3) is equivalent to a total computable decision procedure for Bad(U,m).

Proof from bound to decision. Compute R(U,m), run exact feasibility of (1) for the finitely many j=0,...,R(U,m), and return YES iff any succeeds. Every operation terminates. A bounded witness makes YES sound; (3) makes a complete bounded rejection sound over every finite j.

Proof from decision to bound. Decide Bad(U,m). On NO output zero. On YES enumerate j=0,1,... and decide (1) at each j until the first YES; output that j. Positive source enumeration terminates in the YES case because a finite witness exists. Thus the constructed function is total and satisfies (3).

This is the finite-input G3 one-witness/decision equivalence applied to the **marked source exclusion**, with its added predicate explicit. It is not a new asserted master G3 recognizer. No extra positivity margin is required: each bounded-shape RCF call retains the strict inequalities and may sample an interior algebraic witness afterward.

## 3. Exact partial certificate procedure for a supplied candidate

Assume (3). For m=2,3,... decide Bad(U,m). Stop at the first NO and return the inherited finite legal rooted-topology tester recovering Gamma_(L,m).

**Theorem E.** This is a sound partial algorithm, and it halts if and only if U has mathematical finite forcing against every finite positive rival in this private class.

Soundness. At a NO, no admitted source can match U's complete capped kernel and lie outside the all-copy normal form. The original finite legal tester recovers precisely that complete kernel; every rival matching its responses must therefore agree with U on the entire original private passive menu.

Termination in the forcing case. A finite legal determining family has a finite entering-root cap M. Every rival matching U's complete cap-M kernel substitutes identically into every context in that family. Since the family is determining, no later-inequivalent rival exists at cap M. Thus Bad(U,M) is false, and the loop reaches a NO by then. Alternatively one may take mathematical forcing directly in the complete-cap formulation supplied by tomography/composition.

Necessity of the forcing case. A halt returns a sound finite determining tester by the soundness argument, so U is finitely forced. If U is not finitely forced, every cap has a later-inequivalent matching rival and every decision is YES. The algorithm runs indefinitely and does not falsely accept a plateau.

No uniform-in-m bound was used. The separate mathematical existence of a determining prefix guarantees the loop's eventual NO; (3) only makes each individual test decidable.

If a positive source theorem independently establishes forcing for every supplied candidate in some effectively specified class, this partial algorithm becomes total there. A nonlinear all-fibre forcing theorem could provide that premise even if its original proof is nonconstructive. It does not have to yield a witness-size bound uniform in m merely to be effectivized by Lemma D.

## 4. Observation-only semidecision of the forcing regime

Use the countable, effectively encoded algebraic legal family and same-graph/density hypotheses of Theorems A/B in the companion. The actual target T is one finite admitted private source; its description and rival-size bound are not supplied. Every requested response is returned as an effective algebraic number.

Enumerate every finite positive algebraic candidate U. Dovetail the partial certificate procedure in Section 3 for all candidates. For each returned finite determining tester C_U, compare its responses exactly with the target's response values. Return the first matching (U,C_U).

**Theorem F.** Under (3), this observation-only algorithm is sound and halts if and only if the target is mathematically finitely forced in the stated private class.

Soundness of an accepted match. C_U is sound against all unknown-size private rivals. T is one such rival, so its match implies U and T agree on the whole menu. Every V matching T on C_U matches U there and hence agrees with both everywhere. Thus C_U determines T.

If T is finitely forced, the companion's same-graph full-profile theorem supplies one finite algebraic U* equivalent to T. Its identical law makes it finitely forced too. Exhaustive enumeration reaches U*, Section 3's procedure halts on U*, and the exact target comparisons pass. Dovetailing prevents non-forcing earlier candidates from blocking termination.

Conversely, an accepted certificate makes T finitely forced by the soundness argument. Therefore a target with exact rivals after every finite prefix cannot be incorrectly accepted; this procedure supplies no finite terminal negative verdict for that case.

Even weaker coverage suffices in the forcing case: if a finite forcing prefix of T has algebraic values and the fixed actual graph has a K-semialgebraic domain, the earlier finite-input same-graph algebraic-witness theorem gives an algebraic U* fitting that prefix. Forcing then makes U* equivalent to T on all legal responses. This is an existence argument, not permission to query arbitrary-real responses using algebraic encodings.

This establishes a conditional **semidecision of the positive forcing regime**. If all target laws in the claimed branch are separately proved finitely forcing, it is the desired total positive stopping algorithm for that branch. The mathematical forcing property and (3) are both still open for unrestricted positive private INDEPENDENT words. The original full graph/shared-register/coarsened-menu master needs more than the private normal form, so no general G4 closure is claimed.

## 5. What extends and what does not

The same proofs apply to any effectively enumerable admitted source family for which, on every supplied candidate/shape pair, the entire authorized equality locus is effectively semialgebraic and the original finite compiler is available. Shared variables and joint registers must remain in that actual equality relation. Theorems A/B already give coverage for arbitrary finite polynomial graphs under their response/density premises; the private predicate R_(U,j) is what currently limits this effectivity application.

For general original graph pairs, a fixed finite ring gives an abstract finite equality prefix but does not compute its all-copy relation. An unknown relation cannot be inserted into (1) as though it were a finite RCF formula. For a weaker authorized channel, use its actual equality relation rather than the richer full-kernel R_L. A randomized-only row does not authorize its summands.

Ordinary G3 recognition and (3) are distinct questions. The source-local exclusion is not a new scientific actuator, but a G3 procedure whose input language only accepts unmarked observation values need not handle it. Proving decidability for each fixed future disagreement marker likewise does not decide (2), since the existential later-experiment quantifier remains unbounded unless the supplied equality relation removes it.

## 6. Direct compression attack and current blocker

The attempted route was to compress a bad prefix by running an ordinary one-witness G3 search, then apply the supplied-shape normal form. It fails exactly because U is already in the prefix fibre; preserving a source outside R_U is indispensable. Replacing the future marker by NOT R_U repairs the finite per-shape predicate, but no source-faithful small-word replacement preserving that predicate has been proved.

Two routes now separate cleanly:

1. Prove a uniform b(U) preserving NOT R_U across every m. This proves finite forcing and, if effective, computes certificates directly as in0846.
2. Prove the finite-input bound R(U,m) for NOT R_U and independently prove finite forcing by a source-positive full-fibre argument. The present companion combines those results into detectable observation-only stopping without a target description.

Neither route may use a closure point, a signed ordinary-time factor, a latent count readout, a source with parameters changing across coordinates, or a generic matrix witness. The exact all-cap ordinary full-return/hazard alternative stays open. No all-size witness bound was computed or established in this packet.

The next mathematical task remains an actual exclusion-preserving source compression theorem or a finite full-fibre forcing certificate. This packet records the exact G3 input proposition that would suffice; it does not report that proposition proved.
