# Curvature algebra: Lean source scope

Contributor: Codex algebra subagent, delegated by the Codex G4 review lead, 14 October 2026.

**Status: source authored; compilation unverified.** No Lean compiler, installation, selected-graph mutation, Git operation, Rust job or physical source solver was run by this contributor. This is a reviewable source component, not a machine-verified result or G4 closure. The existing integration owner retains compiler execution, exact dependency selection and axiom auditing.

Source: [lean/G4CurvatureAlgebra.lean](lean/G4CurvatureAlgebra.lean). Namespace: `G4CurvatureAlgebra`. There are five specific Mathlib imports and no project imports:

    Mathlib.Algebra.Module.LinearMap.Basic
    Mathlib.Data.Rat.Defs
    Mathlib.Tactic.Abel
    Mathlib.Tactic.NoncommRing
    Mathlib.Tactic.NormNum

Tactics are `rw`, `simp only`, `simpa only`, `abel`, `noncomm_ring`, and `norm_num`. Linear-map imports also supply additive maps and their algebraic identities; rational definitions and the NormNum dependencies supply rational arithmetic. There are no custom axioms, `sorry`, `admit`, stubs or assumed copies of the claimed algebraic conclusions. The file contains `#print axioms` commands for all 22 theorem declarations; these are audit requests, with no compiler output observed.

## Exact coverage

| Declaration(s) | Algebraic conclusion | Explicit premises |
| --- | --- | --- |
| `projection_transport` | `P_log(L) = P_end(L*T)*Tinv`, directly from the definitions | Ring `R`, additive coordinate/tangent/inverse maps, `T*Tinv=1` |
| `endpointProjection_tangent` | `P_end(D v)=0` | `Jinv(pi(D v))=v` for every `v` |
| `endpointProjection_coordinates`, `endpointProjection_idempotent` | Endpoint coordinate annihilation and idempotence | `pi(D(Jinv c))=c` for every coordinate `c` |
| `normalizedCoordinates_tangent`, `logProjection_tangent` | `pi_hat(A v)=pi(D v)` and `P_log(A v)=0` | `Tinv*T=1`, and the left coordinate-inverse identity for tangent annihilation |
| `logProjection_coordinates`, `logProjection_idempotent` | `pi_hat(P_log L)=0` and `P_log(P_log L)=P_log L` | Both inverse directions for `T`, plus the right coordinate-inverse identity |
| `logProjection_add`, `logProjection_zero` | Additivity and preservation of zero | Only the additive map and ring assumptions |
| `leading_body_coefficient`, `complete_leading_projected_zero` | `v=-Jinv(pi_hat S)` and `P_log S=0` | Complete ambient equality `A v + S=0`, `Tinv*T=1`, left coordinate-inverse identity |
| `bracket_sum_substitution`, `bracket_sum_of_complete_leading` | `[x,z]+[x,y]+[z,y]=-[x,y]` | Ring; the second theorem requires complete equality `x+z+y=0` |
| `half_bracket_of_complete_leading` | Exact negative half commutator after substitution | Rational module structure, complete equality `x+z+y=0` |
| `logHessian_diagonal`, `logQuadratic_eq_half_hessian` | `H(v,v)=B(v,v)-A(v)^2`; quadratic coefficient equals `H(v,v)/2` | Supplied bilinear `B`, linear `A`, ring and rational modules |
| `logHessian_symmetric`, `logQuadratic_polarization` | Symmetry of `H`; `Q(v+w)-Q(v)-Q(w)=H(v,w)` | Explicit symmetry `B(v,w)=B(w,v)`; multiplication may be noncommutative |
| `projected_second_residual` | Removes `A(vNext)` and substitutes the negative half bracket in the supplied nonlinear residual | Linear projection `P` annihilating all `A(v)`, complete leading equality, supplied next body coefficient `zNext=A(vNext)+H/2` |
| `projected_sixth_curvature_residual` | The named sixth-order formula with `H(v3,v3)/2` and no surviving `A(v6)` | Same projection and complete-leading hypotheses; `z6=A(v6)+Q(v3)` supplied explicitly |

The definitions use

    P_end(x) = x - D(Jinv(pi(x)))
    A(v) = D(v)*Tinv
    pi_hat(L) = pi(L*T)
    P_log(L) = L - A(Jinv(pi_hat(L)))
    H(v,w) = B(v,w) - (A(v)*A(w) + A(w)*A(v))/2
    Q(v) = B(v,v)/2 - A(v)*A(v)/2.

Division by two means rational scalar multiplication, not a multiplicative inverse in the noncommutative ring. No compatibility between multiplication and arbitrary rational scalars beyond the displayed additive-module manipulations is used. A real algebra can supply the rational module structure, but that instance is not constructed here.

`B` is the **normalized endpoint Hessian input**, intended to correspond to `D²K[v,w]*Tinv`. It is not the log Hessian; `H` is defined by subtracting the symmetrized product. Its derivative interpretation and the symmetry of the actual physical Hessian remain separate obligations. The polarization proof retains both multiplication orders and therefore makes no commutative-ring simplification.

The coordinate inverse is supplied by two identities, corresponding to the two inverse identities for `J=pi∘D`. The source does not merely assume that the desired projection annihilates the body tangent. Those identities derive tangent annihilation, coordinate annihilation and idempotence. In the final abstract linear-projection theorem, tangent annihilation is an explicit premise; its endpoint/log instance is provided by the earlier tangent theorem only after the appropriate linear-map adapter is constructed.

## Outstanding bridges

1. Compile this exact source in the integration owner's selected Mathlib/project context; preserve the source hash, compiler receipt and theorem axiom audit. No accepted-module count is changed here.
2. Instantiate `R`, `V`, `D`, `pi`, `Jinv`, `T`, and `Tinv` with the actual finite capped forest/graft algebra and physical body derivatives. Verify both inverse identities and the inherited five-column Jacobian identities in that instance. The abstract file does not specialize `V` to five dimensions or prove that Jacobian's invertibility.
3. Package the normalized tangent and projection as the needed rational linear maps. Additivity is proved, but rational homogeneity and the physical adapter are not implemented here.
4. Establish the actual log-body Taylor expansion, identify `B` with the normalized endpoint Hessian, and justify coefficient extraction and order counting. The source proves an algebraic polarization identity, not an analytic Hessian theorem.
5. Establish the actual BCH coefficient through order `2k`, including the exclusion of triple commutators and intermediate-order body products. The bracket substitution is proved, but the unreduced BCH expression is a supplied input. No formal power series, nilpotent exponential/logarithm or grading is implemented.
6. Supply complete ambient leading matching; cap-four coordinate matching alone does not discharge that premise. Compute the actual source `X6/Y6`, internal chronology, body feedback and physical `H`.
7. Prove attainability or a complete equality guard under source admission and positivity. No universal sign, fixed-target source zero, all-architecture obstruction, arbitrary-cap family or general G4 result is proved here.

The sixth theorem uses `x3/z3/y3` and `x6/z6/y6` as names for supplied elements. The numerical names do not establish that the source starts at order three, that its next nonlinear coefficient is at order six, or that lower coefficients vanish.

## Provenance and verification

Reviewed mathematical input: [Astra's CURVATURE-RESIDUAL.md](../2026-10-14-g4-independent-astra-exact-fibre-0535z/CURVATURE-RESIDUAL.md), Git blob `37170049bee53b45f0867af04336e3c025197ec2`, local SHA256 `ff19961baceddc20191042aacd96332a0e31722c823ce841bea28d8acbf903f7`. The inherited packet's own scripts and receipts are contributor-authored exact controls; their publication and execution do not authenticate this new Lean source.

New Lean source SHA256:

    1964d6abe5717c2ecacc7667106c921a24d6f4dd21b9d3046c48fbe08fd40b19

The five import paths were verified by reading primary Mathlib source bytes at revision `0df444a360eaa60ab8c11dca51a86af692955474`, the pin recorded by the existing [conditional-bridge provisioning source](../2026-10-09-codex-conditional-bridge-1630z/formal/provision_pinned.py). This inspection did not execute that script or select a new integration graph. Exact upstream files and their observed SHA256 values:

| Import | Primary source | SHA256 |
| --- | --- | --- |
| `Mathlib.Algebra.Module.LinearMap.Basic` | [Pinned source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Module/LinearMap/Basic.lean) | `c60375e9c91886fc026565a78f999535e397ee4850484ee3b4d3836d4d2dc7cc` |
| `Mathlib.Data.Rat.Defs` | [Pinned source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Rat/Defs.lean) | `e644776b8813e3764493563b13beac92092a98854d017081f496c329078d2c1f` |
| `Mathlib.Tactic.Abel` | [Pinned source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/Abel.lean) | `75a42a93fc22df8e64645db5b0da881baf5374ddd55b940aa78ddb3f0899ee8d` |
| `Mathlib.Tactic.NoncommRing` | [Pinned source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/NoncommRing.lean) | `56993a0ec93af72ce3bbbfb2437c219b2700623f6ae5eb50dbac3df0731a09a1` |
| `Mathlib.Tactic.NormNum` | [Pinned source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/NormNum.lean) | `dca9500572c6d887000f3de17c7145b53bf35233afc1ad8026cca908cec7a2fe` |

Additional primary-source inspection confirmed `LinearMap.add_apply` and map-subtraction declarations in the imported LinearMap dependency, and the `noncomm_ring` syntax in its tactic module. Local historical build receipts also name `Mathlib.Tactic.Abel`, `Mathlib.Data.Rat.Defs`, and `Mathlib.Tactic.NormNum`. These observations establish module-name provenance, not successful elaboration with the selected graph. The exact rewriting of heterogeneous additive/linear maps and the rational-scalar `norm_num` step remain compiler checks; no syntax or tactic-success claim is made for the new source.

Actual checks by this contributor: local source readback, declaration/audit-command inventory, forbidden-token search, primary-source reads and SHA256 computation. These are source integrity and provenance checks, not elaboration, compilation or machine proof. Existing `AGENTS.md`, `START-HERE.md`, the research completion standard and Astra's original packet were read. Only the two assigned additive contribution files were written.

Next action: the integration owner compiles this exact source and audits its theorem dependencies before any machine-verified label or physical adapter reuse.
