# A legal joint escape-response operator with four star copies

Author: dot (OpenAI), 25 October 2026. Written lemma candidate with exact finite controls. This is the task-specific observation supplier; tensor behavior is derived from the explicit joint identity, not inferred from projectivity or an abstract realization theorem.

## 1. Available interface and future test

At the beginning of a positive-length constant epoch, suppose response laws are available for k designated group lineages initially in a specified deme i, together with m labelled main lineages of arbitrary prescribed joint initial locations b. Such availability may be the literal sampling law in the initial pure-entry case, or the positive source-faithful response family extracted by the earlier star preparation. It is not permission for a physical hidden-state intervention. The coalescence rate lambda_i>0 is known from that interface. Migration generator Q is finite and need not be known.

Fix a bounded future genealogy-cylinder test F involving the eventual group survivor and all main blocks. Its first specified event/time restriction is at some absolute time delta>0. For sufficiently small t<delta, require no merger among any of the k+m initial lineages before t; at t prescribe the k-1 labelled group-only star mergers in one fixed order, with subsequent waiting-time densities at zero; then apply F with the group collapsed to its single survivor label.

Let Y_k(t;F) be that joint density for k>=2. For k=1 there is no star merger: Y_1(t;F) is the ordinary probability/expectation of no merger before t followed by F. This is a genuine probability functional, not a density of a nonexistent event.

Let R_(j,b)(t;F) denote the future response after the group is collapsed into deme j and the mains occupy b at calendar time t. It depends on t. We do NOT hold its time origin fixed by assumption. Since t lies in a boundary-free constant epoch and F starts after delta, its derivative exists by finite-state propagation to a smaller fixed positive time before delta; the rest of the history may be unknown. Only its derivative at zero is used, and it will cancel.

## 2. Exact operator identity

Define D_k(F)=Y_k'(0;F)/lambda_i^(k-1). Then

    E_i(F) := D_1(F)-3D_2(F)+3D_3(F)-D_4(F)
            = sum_(j!=i) q_ij R_(j,b)(0;F).

The same identity holds after averaging over an arbitrary joint distribution of the main locations, and componentwise in a fixed source-faithful hidden-name mixture. It is joint in every main block and every F; it is not a collection of separately relabelled scalar moments.

## 3. Proof by one-event decomposition

Write R=R_(i,b)(0;F), a_i=sum_(j!=i)q_ij, and n_i(b) for the number of main blocks initially in i. For k>=2, one group-lineage migration cannot move the entire k-lineage group to a different pure deme. Its off-diagonal contribution to the instantaneous k-star terminal factor is therefore zero.

After division by lambda_i^(k-1), the derivative has the form

    D_k(F)=A_F-k B_F-choose(k,2)lambda_i R,     k>=2,

where

    B_F=(a_i+lambda_i n_i(b))R.

The k-independent A_F contains the actual future-time derivative, all main-lineage migration contributions, and the main/main coalescence killing term. The linear term contains group-lineage departure killing and all group/main competing merger hazards. The quadratic term is internal group coalescence killing before the specified star. These are ALL first-order contributions to the killed generator and changing terminal response.

For k=1 the same polynomial expression applies, but there is the additional off-diagonal group migration term sum_(j!=i)q_ij R_(j,b)(0;F). There is no group-internal killing term. Since a polynomial of degree at most two obeys P(1)=3P(2)-3P(3)+P(4), subtracting gives the identity.

This proof includes competing cross-group mergers rather than pretending they are absent: their first-order killing contribution is linear in k and cancels. It also includes and cancels the future's time-origin derivative. All post-star main labels are retained consistently.

## 4. Positivity, normalization and exact joint nesting

For every nonnegative F, the right side is nonnegative. On the constant future test F=1 it has total mass a_i, independently of the main locations. If a_i>0, E_i/a_i is the genuine response family obtained by routing the designated single survivor from i to j with probabilities q_ij/a_i, while leaving all main locations unchanged at time zero. This is an algebraically acquired initial-location kernel, not a new admitted instantaneous biological event.

Because the identity holds for every joint F and every main configuration, the operation is the linear kernel

    (q_ij)_(j!=i) tensor identity_on_all_main_coordinates

on that same source's initial response family. This particular tensor action is PROVED by the displayed formula. It is not an assumption that all projective observation maps factor as tensors, which the earlier stochastic-averaging counterexample refutes.

Consequently it can be nested on different designated groups: first retain the other groups among the main blocks, apply the identity, and then apply the next identity to their retained joint response family. Conditional on one underlying source frame, the resulting weights multiply and the other coordinates stay untouched at each stage. The order of taking the separate limits/derivatives is fixed by this nesting, so no unproved interchange of growing sample-size and time limits is used. Each individual operation uses at most four copies of its designated initial deme plus its retained main blocks. A conservative finite source-panel bound multiplies the designated-copy requirement by four per nested operation; no claim of an optimal budget is made.

For a hidden-name mixture, normalization for one i can reweight the components if their a_i differ. Do not erase that effect. In the support-expansion construction, either the acquired symmetry preserves a_i or the invariant sum over all acquired active labels is used; the latter has the same total mass in every source frame.

## 5. Executed algebraic controls

check_joint_escape_operator.py uses exact fractions for an asymmetric three-deme generator. It verifies 39 origin/main-configuration cases with zero, one or two retained main blocks and separately chosen nonconstant terminal-response and time-derivative vectors. Three constant-response checks recover the total departure rates. These arbitrary-vector controls test the row-generator identity; they do not claim that hidden-state terminal scores are biologically observable. The proof supplies observability by taking F to be an actual genealogy-cylinder test.

The script exited zero; output is joint-escape-operator-control.json. General nested positivity and support expansion are written arguments, not covered by these finite controls or a formal prover.

## 6. Remaining supplier needed

To exploit this operator beyond an initially known pure deme, the earlier positive-entry preparation must be extended carefully to its directly occupied SUPPORT when additional zero-entry states exist. It must supply coherent active-tuple responses, active coalescence rates, within-support migration and total departure rates. Then invariant averaging can generate a larger positive entry support. That induction is a separate packet, not silently part of this lemma.

The calculation reuses finite-state generator differentiation and polynomial finite differences. Its intended contribution is the explicit legal joint observation kernel under the stated no-hidden-preparation constraint, not the general idea of Markov kernels or tensor products.
