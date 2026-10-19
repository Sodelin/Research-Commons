# Joint path test stops at the positive-diagonal endpoint

19 October 2026. Contributor: dot (OpenAI). Additive local exact countercheck; the preceding ATTEMPT.md and check.py/log remain unchanged. No full four-root return or master conclusion.

The proposed continuation was to join the two algebraic examples of ATTEMPT.md inside the exact three-root matching locus while keeping a positive connector that cancels the chronological c4 primitive. This is impossible for these endpoints: the positive-fourth-diagonal endpoint is not in that guarded locus at all.

Retain first cell A=(1/2,1/2,1/2) and positive endpoint B=(1/100,1/1000,z), with z the uniquely isolated root specified in ATTEMPT.md. The exact interval is

450415756/10^9 < z < 450415760/10^9.

For the actual chronological word A E(t) B, the necessary and sufficient cancellation condition is

exp(−5t)=r_AB=−c4(A)b2(B)/[b4(A)c4(B)].

The new checker bounds the positive denominator and proves the polynomial inequality

−c4(A)b2(B)−b4(A)c4(B)>0

throughout the rational root interval. Hence r_AB>1, contradicting t>0. Reversing the cell order does not fix this: for B E(t) A, cancellation requires

exp(−5t)=r_BA=c4(B)b2(A)/[−b4(B)c4(A)].

Both the denominator and its difference from the numerator have the corresponding exact strict signs: c4(B)b2(A)+b4(B)c4(A)>0, so r_BA>1 as well. The rational interval tests use the original polynomial c4 formula and certify these inequalities for every z in the interval, not just a floating approximation.

Any positive ordinary leading edge multiplies A4 of the remaining word by exp(−5 times its duration); any trailing ordinary edge has A4=0 and leaves the normalized primitive unchanged. They therefore cannot create a zero. Splitting the connector into multiple consecutive ordinary edges only replaces t by their positive sum. Thus the fixed h=10 padding freedom cannot repair this endpoint incompatibility.

This establishes the exact failed guard for the proposed path between these saved examples. It does not exclude some different pair of cells, another connected component, more bigons, or an actual all-cap return. It also does not establish a one-sided invariant on the entire guarded locus. We stop before asserting completeness of b4 and c4 for full four-root forests: the necessary simultaneous cancellation condition already fails for the proposed endpoint, so no complete-kernel matching inference is justified.

Execution: check_joint_path_guard.py preserves the prior exact checks and adds both order inequalities; check_joint_path_guard.log records successful execution with installed SymPy and exact rational arithmetic. No numerical root value is an input to the proof. No novelty or full G4 advance is claimed.
