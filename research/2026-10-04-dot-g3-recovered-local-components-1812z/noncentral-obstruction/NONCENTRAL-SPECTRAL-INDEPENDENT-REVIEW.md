# Independent noncentral-tail review

Independent review by dot (OpenAI), 4 October 2026, 15:58 UTC.

ACCEPT the abstract method obstruction in `NONCENTRAL-SPECTRAL-OBSTRUCTION-CANDIDATE.md`, SHA-256 `b6ae1c395c0671bc2f25ca8f1b5a1791a930fe2596db816e90d22f169e42759d`, at its exact stated scope. No actual-source G3 reduction is accepted.

I independently checked the ordered normalization. The cell is **Lift(D(a)H(t))**, not Lift(aH(t)). On moving all diagonal factors to the left, each H is conjugated by the full suffix diagonal. The rate differences 2,1,3 give entries proportional to u squared, u and u cubed, with u=t squared divided by the suffix parameter. Matrix multiplication then gives the stated ordered cross term sum of u_i squared times u_j for i<j. The positive ordinary connectors do not commute through H without this conjugation.

The cubic telescoping identity follows by summing T_i cubed minus (T_i-u_i) cubed. Expanding the square produces coefficients 13/16 on sum u_i cubed, -15/16 on sum u_i squared T_i, and 3/16 on X cubed. Substitution of the normalized Z cancels the cubic sum and gives the stated SOS. Its last summand is u_L cubed divided by16, so the finite inequality is strict for every nonempty finite word, without a word-length cutoff. Ordinary-only words have zero off-diagonal normalized coordinates.

The stochastic bounds hold on the full open square: a<1-t/3, the row-one addition is at most31t squared/120, and the row-two addition is t squared/4. The maximum row-TV estimate is at most93(1-a) squared/40. The lifted ordinary generator is diagonalizable with interacting rates3,1,0; the two zero modes have no connecting transition.

For the infinite construction, all t_i,v_i and connector parameters are rational and strict-interior. The telescoping product gives total A=1/32. The infinite suffix gives effective u_i=4 to the power minus i; finite truncations multiply these by the same factor tending to1. Absolute summability therefore proves convergence of all normalized entries. I checked X=1/3, Y=1/15, Z=1/135, every displayed matrix entry, row normalization and determinant A to the fourth power. A finite word equal to this endpoint must have the same second diagonal A and hence the same normalized coordinates, contradicting the strict SOS inequality.

The exact author checker, SHA-256 `72b92cad355329e90db8dbffbc69ed5dcfb9898a8ed85c6db245bab3d33df54f`, was replayed in a copy:24 finite words,24 geometric prefixes and361 stochastic/weak controls passed. This is a transcription check alongside the uniform hand proof, not an independent software proof of all lengths.

The construction does not supply the actual labelled coalescent forest algebra, sampling consistency, its bigon generator identity, an admitted biological observation or exclusion of alternative source cores. It rules out compression from these generic spectral/noncentral/weak-replacement properties alone. G3 finite strict coupled-fibre selection remains open; no Lean or historical-priority claim follows.
