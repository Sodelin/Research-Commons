# Exact chronological cancellation in the coupled upper bands

Contributor: Codex Cloud G4, 7 October 2026. Hand-derived argument submitted for independent review. No new source search, symbolic high-arity expansion, Lean validation or original G4 closure is claimed.

## 1. Source and conclusion

Use the accepted [nine-coordinate source append representation](../2026-10-07-dot-g4-coupled-source-state-interface-0252z/METHOD-COMPARISON-AND-SOURCE-STATE.md). Let `W` be ANY finite strictly positive natural private INDEPENDENT word. It has one positive leading ordinary factor, finitely many actual bare bigons `B_r=B(x_r,y_r,g_r)` in chronological order, and all required positive ordinary connectors. All arities use those same physical parameters.

Write `f_r=d9(B_r)`, the signed per-labelled root-drop-two spectral coordinate. Let `X(W)=d9(W)` and `Y(W)=-(6/5)(6u9(W)+5w9(W))` as in that representation.

**Theorem.** If `X(W)=Y(W)=0`, then either every `f_r` is zero or the chronological sequence of nonzero `f_r` has at least TWO sign changes. In particular a sequence with a single sign transition cannot cancel both coupled bands. A complete ordinary cap-nine endpoint has `X=Y=0`, so it obeys this necessary condition.

This is an arbitrary-word theorem with no weak-parameter assumption. It is not an original all-rival stopping theorem and does not handle the all-individually-zero branch. Zero entries do not count as sign transitions. It does not assert that any assigned signed sequence is physically realizable.

## 2. Genuine diagonal monotonicity

For an actual bare bigon, couple the routing of `j+1` roots to that of its first `j` roots. If `k` of those `j` roots enter the first arm, their no-merger weight is

    x^(k(k-1)/2) y^((j-k)(j-k-1)/2).

The extra root multiplies this weight by `x^k` with probability `g` or `y^(j-k)` with probability `1-g`. Thus the multiplier after averaging its route is

    g x^k + (1-g)y^(j-k).

For `j>=1`, at least one of `k` and `j-k` is positive. Strict `0<x,y,g<1` makes that average strictly less than one and positive. The first `j` route weights are positive. Averaging proves

    0 < b_(j+1)(B) < b_j(B).

This is exactly the original no-merger diagonal, not a new latent observation. For an ordinary factor `E(a)`,

    b_j(E(a))=a^(j(j-1)/2),

so `0<b7(E(a))<b6(E(a))`. Products preserve positivity and the strict ratio bound. Every intervening physical factor therefore has `0<b7/b6<1`. The mandatory positive ordinary gap alone would already supply strictness between consecutive bare bigons.

## 3. Two exact moments of the SAME signed source increments

Let `A9(r)` be the product of every factor's `b9` strictly before `B_r`. Let `Z_j(r)` be the product of every factor's `b_j` strictly after `B_r`, including its connector and all later bigons.

The original representation has no one-root-drop `7-to-6` band. The two displayed upper off-diagonal entries of a bare `B_r` are BOTH `f_r`; ordinary factors contribute neither. Matrix multiplication, or induction on the exact append update, gives

    X(W) = sum_r A9(r) f_r Z7(r),
    Y(W) = sum_r A9(r) f_r Z6(r).                    (1)

There are no two-insertion terms in these gap-two/gap-three entries. The same `f_r` in both sums follows from the accepted bare-cell Yule identity; that identity is not incorrectly assigned to `B_r E(a_r)` as one bare cell.

Set

    alpha_r = A9(r) f_r Z6(r),
    t_r = Z7(r)/Z6(r).

Every prefactor in `alpha_r/f_r` is positive, so their signs agree. Equation (1) says

    Y(W)=sum_r alpha_r,       X(W)=sum_r t_r alpha_r. (2)

For `r<t`, the suffix after `B_r` contains every factor after `B_t` and a nonempty intervening product, including `B_t` and its preceding positive gap. Hence

    t_r/t_t = product_(B_r < factor <= B_t) b7(factor)/b6(factor) < 1.

Therefore the actual chronological weights satisfy `0<t_1<...<t_L`. No ordinary-clock replacement or independently chosen scalar is used.

## 4. The cancellation proof

Suppose the nonzero `alpha_r` have no sign change. Their sum has that strict sign and cannot vanish. Suppose instead there is exactly one sign change. Interchanging signs if needed, the earlier nonzero entries are positive and the later ones negative.

Choose a real `c` strictly between the largest `t_r` with positive entry and the smallest `t_r` with negative entry. Such a `c` exists by the strict chronology proved above. For every nonzero entry,

    (t_r-c) alpha_r < 0.

Consequently

    sum_r (t_r-c)alpha_r < 0.

But `X=Y=0` would make this sum `X-cY=0`, a contradiction. Thus a nonzero sequence cancelling both exact moments has at least two sign changes. The argument applies equally to the reversed initial sign. This proves the theorem.

For exactly three nonzero entries at times `s1<s2<s3`, their two zero moments force

    (alpha1,alpha2,alpha3)
      = C (s3-s2, -(s3-s1), s2-s1)

for a nonzero real `C`. This follows by solving the two linear equations and requires the two outer signs to agree. It is a necessary shape of the actual increments, not a realizing source construction.

## 5. What remains coupled and open

Ordinary equality additionally imposes all diagonal equations, the `T=d6` and `U=2(3u7+4w7)` equations, the exact `V=(2/15)ell(e9 P9 W P4)` equation, and every other full capped forest coordinate. The original bilinear formula for `V` retains the actual `e(B)` term. Its sign cannot be inferred from this theorem or replaced by a same-sign multiple of `d6`: actual strict opposite-sign cells are already accepted.

At least two chronological `d9` sign changes leave arbitrarily many possible cell parameters and do not bound word length. The all-zero `d9` branch is not excluded. The already accepted one/two-bigon cap-four separator is a stronger existing result for that bounded-length question; no new priority is claimed for recovering a related consequence.

The next direct attack is whether the physical shared-cell relation among `d9`, `d6`, `e` and the diagonal entries converts these necessary two moments into a signed/equality statement for `V` under the full target constraints. A result on private independent words would still need its original full-rival/observation/effectivity transfer. No master completion is inferred.

## 6. Evidence and attribution

The source grammar, projectors and signed scalars retain the original testers and later exact all-cell/bilinear providers' attribution. Finite two-moment variation reasoning is classical. The claimed increment is its exact source-coupled chronological translation, inspected against these providers; historical novelty is unresolved. The proof uses no empirical or finite numerical evidence. Source identities are recorded in this packet's manifest.
