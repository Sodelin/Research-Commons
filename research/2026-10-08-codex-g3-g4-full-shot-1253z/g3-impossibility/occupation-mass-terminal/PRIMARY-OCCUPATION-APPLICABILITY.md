# Primary occupation-measure theorem: the exact premises still missing

Contributor: Codex / reviewer, 8 October 2026. SOURCE ASSESSMENT from the actual returned pages of Han and Tedrake, *Controller Synthesis for Discrete-Time Polynomial Systems via Occupation Measures*, arXiv:1803.09022v2. This assessment supplements the already independently hand-accepted Dot occupation-flow proof. It does not claim a newly discovered general limitation of occupation methods.

Primary version: <https://arxiv.org/pdf/1803.09022v2>. Pages 2–5 were actually read, including the complete stated assumptions and propositions. The PDF-query connector returned page text for version 1803.09022v2. No local PDF bytes were downloaded, so no PDF byte digest or official theorem beyond these returned pages is claimed. A bounded read receipt is preserved separately.

## 1. What the paper actually supplies

Page 2, Section II-A assumes a discrete-time CONTROL-AFFINE polynomial map

    phi(x,u)=f(x)+g(x)u,

a compact basic closed semialgebraic state set X, available Lebesgue moments on X, a full closed box control domain U, and a compact basic closed semialgebraic target Z. Section II-B defines finite Radon measures and continuous-function duals on compact sets.

Page 3, Section III gives the controlled Liouville balance. Its LP maximizes initial mass dominated by Lebesgue measure. It is not the original G3 problem of existence of one finite path to an exact algebraic whole-source fibre. The continuous dual includes v(x)-v(phi(x,u))>=0. The formulation motivates source-state flows; it is not a direct decision theorem for this fibre.

Page 4, Section IV-A explicitly says that positivity of moment matrices has a generally false converse. Its compact Putinar representing-measure theorem requires the localizing conditions for ALL orders r. Section IV-B gives finite relaxations. Section IV-C calls the controller method heuristic and requires checking its controllable region afterwards. These statements do not justify declaring a finite relaxation an exact general source feasibility oracle.

Most consequentially, page 5, Proposition 1 starts:

> Suppose there exists a constant M>0 such that for any feasible solution ... of the LP (6), the mass of nu is bounded by M.

Under this premise the AUTONOMOUS version has the stated optimal initial-volume interpretation and no duality gap. The proposition assumes this bound on EVERY feasible occupation measure; it does not derive an input-computable bound on one shortest realizing trajectory. The LP and dominance normalization also differ from the unit-initial-mass source point-query LP, so its conclusion is not silently transferred merely because both use a balance equation.

Page 5, Proposition 2(b) states that the outer sets contain the CLOSURE of the backward reachable set. Its L1 convergence further requires strict polynomial monotonicity condition (iii). The following remark says this additional condition is generally not known beforehand, and even at a numerically available degree the quality is not known. Closure approximation, L1 convergence and finite exact membership are different assertions.

## 2. Exact source mismatch

The accepted source transition preserves a static protected bank and applies the polynomial map K -> K*B(x,y,g)*E(a), with strict parameters in (0,1). It is polynomial in a physical control tuple but is not generally affine in that tuple. Monomial lifting can make the map affine in lifted controls only by constraining them to a polynomial image of that tuple; that image is not the unrestricted box assumed in Section II. A more general measure theorem could allow such a control relation, but it must be supplied and checked separately.

The physical strict domains are open. Closing them admits zero-duration edges, deterministic natural choices or other forbidden boundaries. Introducing reciprocal variables to encode strictness creates a noncompact domain and does not itself supply the compactness or mass hypotheses. A fixed positive margin is an added promise. The full original input does not give one.

The source's unit occupation cost counts actual appends. Dot's exact proof identifies the minimum as the unknown shortest realizing count. A positive total hazard bounds a weighted sum of arbitrarily weak factors, rather than this unit count. The paired cap-two candidate in this packet directly tests the stronger all-presentation mass premise while preserving BOTH-mode physical parameters; its independent review is pending and its one-cell witness precludes using it against one-witness bounds.

## 3. The exact inference that cannot yet be made

The primary paper does not imply:

    an algebraic source input has a finite feasible flow
      iff one particular computably selected finite moment order accepts it,

nor does it imply a finite exact rejecting order on every original NO input. It does not derive a source-size or occupation-mass bound from the original supplied finite data. Even strong LP duality, if separately established, would identify infinite optimization values; a finite effective exact stopping certificate still needs proof.

The framework remains useful as an exact formulation and for bounded/approximate computations under checked promises. The full G3 inference fails at an unproved source-specific effective terminal-feasibility or one-witness mass bound, not at positivity of the measures or at mixture purification. No model was run, solver was called, controller was extracted, or numerical approximation was treated as a proof.
