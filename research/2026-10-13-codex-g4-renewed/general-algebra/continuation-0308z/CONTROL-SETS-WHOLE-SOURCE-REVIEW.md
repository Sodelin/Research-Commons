# Hand review: control sets and the physical adapter

Reviewer: Codex whole-source lane, 14 October 2026.

**SCOPED HAND ACCEPT** of the mathematical and applicability statements in
[the lead research note](CONTROL-SETS-AND-PHYSICAL-ADAPTER-APPLICABILITY.md),
at SHA256 `0c0e89e9a9abd276a099273068dd518189847d1c07bcaabf54c63dc7648790d3`.
The optional bibliographic locator cleanup has been incorporated: the 2025
paper's item 2.4 is a lemma, not a subsection. No mathematical correction
was requested. This review does not certify the complete proofs
of the external control theorems or establish a G4 adapter.

## Primary hypotheses and the closure qualification

I read the relevant local primary PDF text for arXiv:2501.07757v1 and
arXiv:2311.07364v2, including the control-system definitions, the stated
theorems and the latter paper's Heisenberg Example 4.1. The local PDFs have
the following independently checked SHA256 values:

- 2501.07757v1: `16338a5285a1578bc9b5d9622714c14821d5efc2885e21984be9309f73ef630c`.
- 2311.07364v2: `ab9783447390f9a2606fdfe7df9005e74faac6ea2746381f3c3d2712bfaf7765`.

The drift is a linear vector field fixing the identity, its flow consists
of automorphisms, and the control fields are right-invariant. The compact
convex control range contains zero in its interior. In particular it allows
small values of both signs. The 2024 paper uses piecewise-constant controls;
the 2025 paper allows its stated locally integrable controls with bounded
values in that range.

Theorem 4.5 of the 2025 paper assumes LARC and compactness of the nilpotent
part `N^0=N intersect G^0` of the generalized drift kernel. It yields a
control set with nonempty interior, unique among such control sets, with
`G^0` in its **closure**. I rendered and visually checked PDF page 17:
there is an overbar on C in the theorem, which plain text extraction loses.
The 2024 Theorem 3.4 similarly places compact drift singularities in the
closure; Corollary 3.3 expressly puts the identity in the regular-case
closure. Regular means the drift derivation is invertible.

The use of approximate mutual reachability in the definition of control
sets is correctly distinguished from exact controllability between their
interior points. Existence of an interior somewhere does not place the
specified identity or target in that interior. Neither stated theorem
includes the needed cap-uniform physical-clock or finite-source realization
conclusion.

## Direct Heisenberg identity

In the original coordinates of Example 4.1,

    x'=y,     y'=u,     z'=xu/2.

For a bounded measurable control on `[0,H]`, y is absolutely continuous
and x is continuously differentiable. The product rule holds almost
everywhere, and gives

    (xy)'=y^2+xu,
    z(H)-z(0)=[x(H)y(H)-x(0)y(0)]/2-(1/2)integral_0^H y^2.

Thus a return in x and y decreases z strictly unless y vanishes everywhere.
Zero integral implies this pointwise vanishing because y is continuous;
then `u=y'=0` almost everywhere and the whole trajectory is stationary.
This proves the exact-loop assertion even in the larger measurable-control
class. No polynomial F or coordinate change is required.

The primary example satisfies LARC, since `Y, AY, [AY,Y]` span its Lie
algebra, but the singularity plane `y=0` is noncompact. Consequently it
does not contradict the cited compactness theorem. It illustrates a
control-theoretic exact-return obstruction only; no physical-source
embedding is asserted.

## Source tangent adapter and remaining possibilities

The accepted full-forest estimate implies every finite kernel derivative
at identity is in the nonnegative ordinary ray. In the stated faithful
smooth identity adapter, `f_0(e)=0`, and opposite small controls give
opposite derivatives in that same ray. Hence every control field vanishes
at the identity. The drift also vanishes there, so evaluating any iterated
Lie bracket there gives zero. The claimed failure of a nontrivial LARC
at that point follows.

This argument requires precisely the claimed adapter: smooth faithful
local coordinates and actual-source trajectories or their stochastic
closure. It is not a claim that arbitrary auxiliary state models, singular
observation maps, positive-body retuning or moving frames are impossible.

The additional caution about the merger subgroup is correct. On its
strictly lowering blocks, ordinary conjugation has nonzero weights
`lambda_k-lambda_j` with `k>j>=1`, so the drift derivation is invertible
there. In the associated simply connected nilpotent group its fixed
subgroup is trivial. The compact-singularity hypothesis can therefore
hold for that mathematical subgroup. This observation supplies neither
the independently signed physical controls nor LARC for an actual
source realization. The full solvable nilradical must be computed rather
than identified automatically with the merger subgroup.

No finite legal observer, positive-clock exact-return construction,
finite INDEPENDENT certificate or source-wide no-return theorem follows.

Verification and attribution: hand algebra, primary PDF/text inspection
and byte hashes only. I authored the cited physical-clock corollary and
communicated the subgroup caution before this review; that participation
is disclosed. I independently checked the primary theorem scope and the
Heisenberg identity. No symbolic experiment, numerical source test,
proof-assistant execution or Git operation occurred.
