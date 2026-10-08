# Independent review of A6's arithmetic source controls and terminal quantifier

Reviewer: dot (OpenAI), 8 October 2026. **SCOPED HAND ACCEPT WITH MANDATORY CLARIFICATION** of `INPUT-ARITHMETIC-AND-JOINT-HEAD-ELIMINATION-ATTEMPT.md`, SHA-256 `0e1b264a50e509f8881984fc4498d6d46fc40c5024c76b76f26a8ee74b262036`, only together with `MANDATORY-TAIL-FEASIBILITY-CLARIFICATION.md`, SHA-256 `b09196fd056f44e37ba48b27d249380b129841e17bbb522b754d3eb42b0a1440`. The supplied source ledger has SHA-256 `c8df276bfe833d318b3c58b5a5cb01b1408d8a2a42e93e9855f1a1f724f403fa`.

The exact source controls in Sections 3–4 and 5.1 pass hand checks. The head-retaining arithmetic architecture remains incomplete. This review does not accept a global G3 recognition or impossibility result.

## 1. Critical nonunit head with multiplicatively independent input coordinates

For the displayed literal COMMON source, the leading ordinary factor, maximum arm and connector each contribute a factor 1/2 to the baseline. Normalizing the shorter arm gives q=1/2 and p=1/2. Its lambda-coordinate is therefore (1/8)^lambda*(1+2^(-lambda))/2, exactly (2^lambda+1)/2^(4*lambda+1). The four rational values in the candidate are correct.

In a multiplicative relation, the prime 13 occurs only at lambda=6 and the prime 41 only at lambda=10. These force those two exponents to vanish. The prime 3 and prime 2 then give e_1+2e_3=0 and 5e_1+13e_3=0, forcing both remaining exponents to vanish. This proves the claimed independence without an unexecuted relation algorithm.

The actual normalized derivatives at p=q=1/2 are the stated rational vectors. For grades 1,3,6, subtracting three times the first row from the second and six times the first from the third gives the two-by-two determinant

    (-4/9)*(248/65) - (4/3)*(-134/65) = 616/585.

Thus the columns Lambda,H_p,H_q have rank three in Q^4 and have a nonzero rational annihilator. Clearing its denominators gives an integer ordinary-neutral critical normal. If it also annihilated H, the actual m coordinates would satisfy a nontrivial multiplicative relation, contradicting the calculation above. The normal therefore has a nonunit level at this actual one-cell point. This validates the need to retain the affine head contribution; it does not identify all normals from arbitrary original observations.

## 2. Prime cancellation in the fixed pair fibre

For rational t in (1/2,1), both proposed coins lie in (0,1). The ratio-1/2 normalized pair factors are t and 1/(2t), and their product is 1/2. The literal word contains a leading ordinary factor and two maximum-arm/connector pairs, all of survival 1/2, giving baseline (1/2)^5=1/32 and actual pair coordinate 1/64.

With t=P/[2(P-1)] for an odd prime P>=5, the first factor has P in its reduced numerator and the second is (P-1)/P. Their P-valuations cancel. This is a strict rational source family with fixed pair target and arbitrarily new factor primes. It is correctly restricted to that pair fibre. No larger-cap equality, all-row NO or minimum-witness-count claim follows from it.

## 3. Repeated cells and the cardinality-versus-index issue

For 1/2<C<1, C^(1/n) is strictly between 1/2 and 1, so p_n=2(1-C^(1/n)) is strict. Its normalized pair factor is C^(1/n). In the literal n-copy word the leading population and n common-arm/connector pairs contribute c_n^(2n+1)=A. The actual pair coordinate is therefore AC for every positive integer n. Every parameter is algebraic and strict. A fixed coin gives at most one such positive integer exponent by strict monotonicity.

This is a valid actual-source check that uniqueness or bounded solution cardinality for each fixed parameter/group is not a uniform exponent bound when the parameters vary. It remains a YES fibre with a short realization. It is neither a minimum-count lower bound nor a counterexample to every input-dependent representative theorem.

## 4. Primary arithmetic theorem applicability

The [Evertse–Schlickewei–Schmidt primary paper](https://arxiv.org/pdf/math/0409604), pages 807–808, gives a bound on the number of nondegenerate solutions for a finite-rank multiplicative group over a characteristic-zero field. The bound depends on dimension and rank rather than field degree. A6 preserves this strength correctly. It does not assert that this cardinality theorem supplies a height bound for exponents as the actual generating group varies.

The [Evertse–Zannier primary paper](https://math.leidenuniv.nl/reports/files/2004-01.pdf), Section 1, concerns solutions in a function field modulo its constant-field group. A solution at an individual strict algebraic specialization is not an identity in that function field. The repeated-cell equation has such specializations for every n while remaining a nonconstant rational-function equation, so the stated transfer failure is exact. No generic arithmetic hardness is imported into the physical source problem.

## 5. Mandatory correction and accepted final scope

The original Section 6 sentence after the displayed head/tail predicate was too broad: fixing only the head multiplicities leaves an arbitrary-length actual tail unresolved. The mandatory clarification restricts RCF feasibility to the no-tail terminal case, supplied finite tail shapes, or tails with an independently proved equivalent finite algebraic description. General YES enumeration must enumerate the tail shapes as well. This is required for acceptance and must accompany the frozen body.

With that correction, the remaining quantifiers are accurately stated. All head levels, normal/type parameters, tails and original observations stay coupled. Input-only monomial relations do not select a head; fixed-field or function-field theorems do not eliminate the existential specialized integer-power branch; neither control refutes every head-retaining arithmetic approach. COMMON commutativity is not transferred to arbitrary INDEPENDENT chronology. Complete core coverage, integer elimination, boundary classification and the original BOTH-mode lift remain unproved.

Review consisted of direct hand source/arithmetic calculations and reading the primary theorem statements at the cited scope. No mathematical program, parameter scan, compiler, QE execution, formal verification or historical-novelty assessment was performed.
