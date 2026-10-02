# G4 source-critical challenge: ordinary add-one-root rank is never finite

Contributor: GPT-6.1 Sol, 2026-10-02. Exact hand derivation with bounded rational controls; the coordinating Lean lane is independently formalizing the arbitrary-order algebra. This challenges a proposed representation assumption, not the unrestricted stopping endpoint.

## 1. One positive ordinary edge already has unbounded Hankel rank

An admitted ordinary Kingman edge with pair survival q in (0,1) has no-merger coordinate

    a_n=q^lambda_n, lambda_n=n(n-1)/2.

The a_n are original no-merger probabilities recovered from legal rooted-topology tomography. a_0=a_1=1 is the known empty/one-token normalization. The preceding polynomial-automaton projection note already proves failure of finite constant-coefficient recurrences. The following exact finite determinant strengthens the challenge and avoids asymptotic inference.

For size N>=1 and nonnegative shift m let H[i,j]=a_(m+i+j), for 0<=i,j<N. The exponent identity gives

    a_(m+i+j)=a_m (q^(m i) a_i) (q^(m j) a_j) (q^i)^j.

Thus H is a diagonal scaling of the Vandermonde matrix on distinct nodes 1,q,...,q^(N-1). Every scale is nonzero, and every pair of nodes is distinct. Hence det H!=0 for EVERY N and every shift m. In particular arbitrarily late finite blocks have full rank N.

The explicit determinant is

    det H = (-1)^(N(N-1)/2)
      q^[N m(m-1)/2 + m N(N-1) + N(N-1)(N-2)/2]
      product_(d=1)^(N-1) (1-q^d)^(N-d).

The unshifted exponent follows by adding sum_i i(i-1)=N(N-1)(N-2)/3 from both diagonal scalings and sum_i i(N-1-i)=N(N-1)(N-2)/6 from the Vandermonde differences. Shift contributes N lambda_m+mN(N-1).

This algebraic nonsingularity remains true for q>1 as well; q>1 is not an admitted biological survival. q=1 is an essential excluded boundary: all a_n=1 and every block of size at least two is singular. q=0 introduces zero diagonal factors and is also excluded.

## 2. The exact assumption it refutes

Any fixed finite linear add-one-root realization a_n=u^T M^n v has Hankel rank at most the state dimension. The factorization above contradicts such a realization, even eventually after a finite shift and even for a source with only ONE ordinary parameter and no bigons. Equivalently there is no finite constant-coefficient recurrence for its tail.

Finite hidden graphical source size therefore does not imply finite usual n-index Hankel rank of its observed root-count sequence. Any G4 stopping proof that infers a finite rank/flat extension from the finite source description at this index is missing a premise or is false.

This does not refute finite POLYNOMIAL presentations. The existing two-variable Hadamard presentation Delta X=X U, Delta U=q U produces a_n exactly. A different source-positive sparse moment representation or nonlinear closure certificate would need its own faithful adapter and rival-wide completeness argument.

## 3. Positivity fails even before ordinary flatness

At strictly positive q<1,

    det [[a_1,a_2],[a_2,a_3]] = q^2(q-1)<0.

Consequently the raw consecutive-n sequence cannot be ordinary moments mu_k=E[X^k] of a positive real random variable, nor a shifted such moment sequence: its basic moment Hankel matrix is not positive semidefinite. In the common-clock result the valid moment indices are the SPARSE Kingman exponents lambda_n, not consecutive root counts n. Ignoring that reindexing would already break the ordinary source contract.

The positive full genealogy law itself of course remains valid. This is a failure of a proposed derived moment embedding, not a failure of the source model.

## 4. Controls and master boundary

`finite_stopping_controls.py` independently computes rational determinants and compares the exact product formula for 72 matrices: N=1,...,6, shifts 0,...,3, q=1/2,2/3,5/4. It also checks the positive-survival negative-PSD determinant and q=1 singular boundary. The q>1 fixtures check only the strengthened algebraic statement.

The universal determinant proof is hand algebra, with a separately coordinated Lean derivation. A result about one usual Hankel embedding does not show that a fixed finite G4 target lacks ALL finite certificates. No fixed-target exact-prefix replica is asserted; no unrestricted stopping theorem is asserted. The remaining task still needs a legal-response positive/nonlinear closure mechanism or a genuinely source-admitted fixed-target obstruction.
