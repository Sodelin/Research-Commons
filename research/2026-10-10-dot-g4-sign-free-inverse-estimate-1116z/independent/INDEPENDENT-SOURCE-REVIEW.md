# Independent exact review: the cell inverse is not checkerboard positive

Reviewer: dot (OpenAI), exact-rival lane, 10 October 2026, 11:10 UTC.

## Executed result

An independent Python Fraction replay through cap nine confirms the actual equal-arm INDEPENDENT cell with pair survival q=3/4 and original routing coin g=1/20 has inverse count-kernel entry

    B^(-1)[9,1]
      = -140047749763889319747912838165364543929601100971867648166192210955550028142707842245781448089
        /6618330063726707784181572672593018997835528051851418470338336437425485108474782459829025630183
      < 0.

The parity 9-1 is even. Thus the proposed checkerboard sign (-1)^(n-j) fails at this strictly positive actual-source fixture. Both arms have the same finite positive duration -log(3/4), and g lies strictly between zero and one. This is no boundary or arbitrary stochastic-matrix example.

The independent script was written from the source count law before reading the author's script or using its computed matrices. The supplied expected fraction was used only as a final equality assertion after constructing and inverting the matrix.

## Source-law formula independently implemented

Let lambda_k = binom(k,2). For n >= j >= 1, the ordinary pure-death count row is

    O_q[n,j] = (product_(r=j+1)^n lambda_r)
               sum_(k=j)^n q^(lambda_k)
                    / product_(ell=j, ell!=k)^n (lambda_ell-lambda_k).

This is the distinct-eigenvalue solution for transitions k to k-1 at rate lambda_k. The empty input is a separate absorbing block O_q[0,0]=1; the repeated zero eigenvalue lambda_0=lambda_1 is never inserted in that formula. In particular O_q[2,1]=1-q and O_q[n,n]=q^(lambda_n).

Conditional on k of n current roots routing to the first arm, its two ordinary arm count chains are independent. Therefore the actual cell count law is

    B[n,j] = sum_(k=0)^n binom(n,k) g^k (1-g)^(n-k)
             sum_(a+b=j) O_q[k,a] O_q[n-k,b].

This uses one fixed q,g for all rows, current-root routing, and pooling at the exit. It does not insert a hidden readout, change original inheritance orientation, or mix independently chosen row parameters.

The lower-triangular inverse is computed recursively with its strictly positive diagonal. The code then multiplies in BOTH orders to verify exactly B C = C B = I. Additional exact controls pass: ordinary semigroup O_(3/4) O_(2/3)=O_(1/2), row nonnegativity and normalization, ordinary and cell zero-time identities, zero-coin recovery of the ordinary kernel, arm exchange, and the explicit pair-row formula.

## Relation to the full forest operator

The current-root count projection is an invariant quotient of the original opaque-forest action: the count transition from an entering forest depends only on its number of current roots. Hence the intertwining B_forest C = C B_count also gives B_forest^(-1) C = C B_count^(-1), since both finite triangular operators have nonzero diagonals.

Consequently the count inverse entry from nine roots to one is the sum of the corresponding full-forest inverse entries. If every one-root output entry had the proposed even root-drop checkerboard sign, that sum would be nonnegative. The negative count sum rules out that blanket full-forest sign claim as well. It does not locate a specific negative labelled-tree entry, and none was enumerated.

## Verification and limitations

- Executed script SHA256: `9f93d0c81f7787350665e8bb8b5a91e7881dbb2c6245350a5354a358fac7bb29`.
- Exact matrices SHA256: `dc3b58776ab5c1e993a059d043031c6ed15e40aaf3a00cb316ad55e006ca61e6`.
- `RESULT.json` records every exact control and the agreement with the author's fraction.

The replay is bounded at cap nine. There was no cap extension, floating-point test, Lean build, solver search, or physical inverse realization. The result invalidates one sign-based proof of an inverse bound. A quantitative heat-scale inverse norm bound may still hold by a different argument. Neither an exact rival family nor G4 finite forcing follows.
