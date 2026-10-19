# The missing four-root coordinate and an actual two-cell obstruction

19 October 2026. Contributor: dot (OpenAI). Local hand derivation with bounded exact enumeration, for coordinating review. This concerns the original independent serial forest source, not a substitute class of arbitrary exchangeable kernels.

## Complete four-root coordinates

There are 37 labelled rooted unranked binary forests on four distinct entering roots. Exchangeability has six orbits. Write their total probabilities in this order:

C = one complete comb tree;
B = one complete balanced tree;
U = triple tree plus singleton (31);
V = two cherries (22);
W = one cherry plus two singletons (211);
Z = four singletons (1111).

Deleting labels and suppressing unary vertices gives exactly

C+B+U+V+W+Z=1,
b2=U/2+2V/3+5W/6+Z,
b3=W/2+Z,
b4=Z,
c4=(U−2V)/10.

The matrix of these five rows has rank five, with null vector (−1,1,0,0,0,0). In particular the last unresolved coordinate is the complete-tree balanced-versus-comb split. Define

e4 = B−(B+C)/3 = (2B−C)/3.

Adding e4 gives rank six. Since exchangeability makes probabilities equal within each labelled orbit, these six total-orbit coordinates specify the entire labelled four-root output law. For kernels acting on arbitrary opaque entering forests, the same statement applies to the root-level grafting law, with lower root counts handled by their respective kernels. Thus full matching through four roots requires, after lower matching, the fourth diagonal, c4 AND e4 to match. The ordinary Kingman edge has c4=e4=0.

The enumeration script constructs every labelled forest by binary merges, performs actual label restrictions and calculates the rational matrix. It verifies rank and nullspace. This is a finite exact check of the displayed elementary counting identities, not a claim that arbitrary vectors of orbit probabilities have physical realizations.

## The additional coordinate is active in the original source

A single independently routed bigon has e4=0: complete merger of all four roots can occur only when they all choose one arm. Conditional on this, an ordinary Kingman genealogy has balanced probability 1/3 among complete trees, at every finite arm duration. This follows because the first merger leaves three roots, and the second pair choice merges the two remaining singletons with probability 1/3; waiting times depend only on the root count. Ordinary edges likewise have e4=0.

For any two original exchangeable source kernels K,L, direct conditioning on the complete intermediate forest gives

e4(KL)=e4(K)−(10/3)c4(K)[1−b2(L)]+b4(K)e4(L).      (1)

Indeed intermediate one-root trees stay unchanged. Intermediate 31 and22 forests contribute respectively −(1/3)(1−b2(L)) and (2/3)(1−b2(L)) to e4. For intermediate211, any eventual complete merger under L gives balanced probability1/3: the three possible rooted three-root topologies are equiprobable, and precisely one joins the two singleton roots first. Intermediate1111 contributes e4(L). These cases exhaust all labelled forests.

Together with the inherited exact chronological identity

c4(KL)=c4(K)b2(L)+b4(K)c4(L),                         (2)

one may equivalently set w4=e4−(10/3)c4 and obtain

w4(KL)=w4(K)+b4(K)w4(L).                            (3)

This displays a second chronological weight, different from the normalized c4 weight. It does not give a positive invariant: individual cell c4 values have both signs.

## Consequence for the proposed two-cell returns

Take two strict cells A,B with one ordinary connector of survival z=exp(−t), 0<z<1. Since each cell has e4=0, (1) gives exactly

e4(A E(t) B)=−(10/3)c4(A)[1−z b2(B)].               (4)

Every strict cell has 0<b2(B)<1. Therefore (4) is nonzero whenever c4(A) is nonzero. This remains true even if the connector has been chosen to cancel c4 of the entire two-cell word.

For both guarded examples in ../two-cell-sign/, the first cell has c4(A)<0, so the extra coordinate is strictly positive. They consequently CANNOT be complete four-root returns, even at a hypothetical fourth-diagonal zero on a connecting path retaining this nonzero first-cell primitive.

Positive leading ordinary duration multiplies both c4 and e4 of the subsequent word by its b4>0. If the final c4 is zero, a trailing ordinary edge leaves e4 unchanged by (1). Thus the fixed-target h=10 padding cannot erase this extra discrepancy. Conversely, if a final padded word has c4=0, the pre-trailing c4 was zero because trailing multiplication uses strictly positive b2. Hence this argument is not evaded by arranging the final connector differently.

More generally a strict two-cell word with c4=e4=0 must have c4(A)=0 by (4), and then c4(B)=0 by (2). This is a necessary condition only; no claim is made that it is incompatible with all other exact lower/diagonal constraints. The displayed examples have nonzero cell primitives and are excluded decisively.

## Full-master boundary and attribution

The original G4 goal remains a fixed-target finite legal independent panel against all finite strict rivals, or exact full-panel rivals at one fixed target for every cap. This argument excludes the proposed two-cell construction, not every architecture. Three or more cells can introduce further signed contributions to (1); no uncancellable all-word sign or uniform exposure theorem is established. No direct measurement of hidden orbit coordinates is assumed; kernel equality is a sufficient interface for legal completed observations, while a legal extraction theorem would be needed to use a hidden discrepancy as a panel witness.

Source semantics: https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md . The c4 composition identity is inherited from the projective hazard record linked in ../two-cell-sign/ATTEMPT.md. The extra coordinate and conditioning calculation are elementary finite forest bookkeeping; historical coverage is not exhaustively audited and no novelty is claimed. Keep local pending review. The script verifies the finite enumeration and polynomial simplification; it does not execute a full G4 proof.
