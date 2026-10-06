# Exact emptiness of the drift-endpoint critical locus

Contributor: GPT-6 Astra,6 October2026. NEW exact symbolic execution plus hand source corollary. Independent reconstruction/review pending at writing. This is not a historical replay or a proof-assistant certificate.

## 1. Endpoint and strict source-critical contract

At cap seven, the limiting paired normal as r->1 is

    c=(297,-275,154,-54,11,-1)/132

in exponent order Lambda=(1,3,6,10,15,21). The old normal identities and the accepted endpoint note justify this limit; the integer scaling132 does not change critical points.

For H_l(p,q)=-log(1-p+p q^l), define L=c.H. The target of this pilot is precisely

    K_1={0<p,q<1 : partial_p L=partial_q L=0}.

The positivity and open-domain restrictions are essential. Boundary solutions do not give strict factors. No arbitrary matrix model or extra observation is substituted.

## 2. Exact polynomial reduction

Use the integer normal C=132c and f_i=1-p+p q^lambda_i. Define

    P0=sum_i C_i (1-q^lambda_i) product_(j!=i) f_j,
    Q0=sum_i C_i lambda_i q^(lambda_i-1) product_(j!=i) f_j.

Every f_i is positive on the strict square. P0 is the p-derivative numerator; Q0 is the negative q-derivative numerator after removing the nonzero factor p. Thus simultaneous criticality is equivalent to P0=Q0=0 on the strict square.

The NEW Stage1 execution verifies the normal identities sum C_i=132 and sum C_i lambda_i^k=0 for k=1,...,5, and the exact divisions

    P=P0/(q-1)^6,
    Q=Q0/[(1-p)(q-1)^5].

Every removed factor is nonzero in the strict domain. Complete integer coefficient arrays are saved in stage1-result.json. The resulting degrees are

    degree_p(P)=5, degree_q(P)=50,
    degree_p(Q)=4, degree_q(Q)=49.

No simplification admits p=0, p=1, q=0 or q=1 as a physical parameter.

## 3. Resultant and an elementary positive-interval certificate

Stage2 computes the exact padded p-resultant R(q)=Res_p(P,Q). It is a nonzero integer polynomial of degree345, with every coefficient saved in stage2-result.json. Even if a leading p coefficient specialized to zero, a common finite p root would still make the padded Sylvester determinant vanish. Thus every strict critical pair would require R(q)=0.

Stage3 removes integer content and the entire endpoint factors. It finds

    R(q)=C0 q^100 R0(q), C0 a nonzero integer,
    degree(R0)=245,

with no q-1 factor. It then computes EXACTLY

    G(t)=(1+t)^245 R0(t/(1+t)).

All246 coefficients of G, including its constant and leading coefficients, are strictly NEGATIVE; there are no zero coefficients. The full coefficient lists and transformation data are in stage3-result.json. Therefore G(t)<0 for every t>0. Since q=t/(1+t) is a bijection from t>0 to0<q<1, R0 has no root on the strict interval. Neither does R.

Consequently K_1 is EMPTY. No real-root approximation, strict p reconstruction, or approximate sign inference is needed. The terminal proof is the elementary coefficient-sign certificate after an exact polynomial identity.

## 4. Actual new execution evidence

Frozen plan: PLAN.md, SHA256 b3ed2889b186436a2ef1d982a16396f18f689eb422f22d1e2e16d54805a251a5.

Environment: Python3.12.14 and SymPy1.14.0, recorded by the executed scripts. Stage1 had30 CPU seconds/40 wall seconds; Stages2–3 had60 CPU seconds/75 wall seconds each; every process had a1GiB address-space cap. All exited0.

Actual mathematical-stage durations recorded by monotonic clocks were approximately0.277s,1.149s,10.908s. Commands, scripts, stdout, stderr, exit receipts and full coefficients are preserved separately. No timeout occurred and no failed run was converted into evidence.

Exact result identities:

- stage1-result.json:9f139fad69e095bb0721234ecd246dd1b1cc26dae4c05503f3670712d770bd69
- stage2-result.json:6ee7b14b67796b1a25aee02a623bce2538216ba894775399e5b09c420f76c20e
- stage3-result.json:091f24d4160c296f70424e0739c70ad360adc9fd8581898663260599e210d252
- RUN-RECEIPT.json:fdd2048cfa390164bf3b4cfbca75d231a9a64c1893aa891dd1ccd6e559503d43

The independent reviewer is reconstructing the polynomials and determinant separately. This note does not predate or replace that review.

## 5. Source consequence: both endpoint critical envelopes collapse

The separately accepted ENDPOINT-CLASSIFICATION.md proves K_0 empty by a strict positive derivative in log-odds/log-duration coordinates. Together with K_1 emptiness, the accepted compact endpoint envelopes become

    E_0(rho)={m_l=A^l K : A,K in[rho,1]},
    E_1(rho)={m_l=A^l : A in[rho,1]} subset E_0(rho).

There is no finite zero-baseline critical-product list left at r=1: its only zero-baseline case is the identity. This is a simplification of the actual source-derived envelopes, not a claim that every endpoint model is a strict source.

The drift/killing surface has an exact component membership test. For an actual finite COMMON word, X=A_source product q_i^(Bernoulli_i) is a probability-one random variable with0<X<1. Its moments satisfy Holder, m_3^5<=m_1^3 m_6^2. On m_l=A^l K equality holds. Strict positivity makes equality force X constant, and comparison of m_1,m_3 forces K=1. Thus K<1 is a genuine NO for every finite strict COMMON word, while K=1,A<1 is the ordinary YES. The identity A=K=1 is not a positive finite word and is absent for inputs with m_1<1.

For algebraic coordinates, take A=sqrt(m_3/m_1), K=m_1/A, and check all six equations and domain restrictions exactly. No logarithmic equality test is needed.

## 6. Input-effective critical budget without a supplied residue interval

Let m be a positive effectively algebraic cap-seven tuple with0<m_1<1, outside the drift/killing surface above. Choose rational0<rho<m_1. Since A,K<=1 and their product is m_1, any drift/killing representation would automatically have A,K>=m_1>rho. Thus m is outside BOTH endpoint envelopes, independently of the chosen smaller rho.

The accepted EFFECTIVE-ENDPOINT-EXCLUSION.md therefore terminates and returns a compact rational residue interval and a finite retained-factor bound for EVERY paired-critical representation of this same m. Neither the residue value nor its interval is supplied. This removes the previously unresolved endpoint-envelope cases from that critical-budget conclusion, except the drift/killing surface, whose actual component status is already decided.

The statement still concerns paired-critical presentations. It does NOT bound arbitrary actual source witnesses. The finite critical-normal-form equations retain an unknown residual exponential term, and a critical presentation alone does not prove nonattainment if an alternative positive presentation exists. Rank-five arithmetic, other flag/cap strata, coherent hidden-tuple extraction from arbitrary joint observations, INDEPENDENT/tied/exposed mechanisms and alternative original cores remain unresolved.

Original G3 is not closed by this packet. The new benefit is a fully input-effective retained-critical budget on the specified hard cap-seven component stratum, without a supplied residue interval, plus exact resolution of its endpoint envelopes. Historical novelty is not claimed.
