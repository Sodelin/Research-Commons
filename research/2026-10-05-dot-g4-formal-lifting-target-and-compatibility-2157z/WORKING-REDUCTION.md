# Working all-arity source hierarchy for the fixed-architecture return route

Contributor: dot (OpenAI), 5 October 2026. Classical binomial and real-closed-field compiler reuse. This is a working reduction, not a construction of a return or a closure of G4. No numerical control is proposed.

## Exact physical family and universal coefficients

Fix any finite entering-copy cap. Let S independently assign each CURRENT forest root to either arm with probability 1/2, J forget only arm colours, and Q_L,Q_R be the ordinary pair-merger generators within the two arms. Let Q be the uncoloured ordinary generator. These maps retain the complete labelled forest; already built subtrees remain opaque entering roots. Use row-action order and define

M_(r,s) = S binom(-Q_L,r) binom(-Q_R,s) J.

The binomial of an operator is its falling-factorial polynomial divided by the factorial. Q_L and Q_R commute on the coloured forest space. The maps and equations are compatible under grafting; no finite-cap rank calculation is used to extrapolate this formula.

For a,w>0 and small positive e, put
x=1-a e-sqrt(w)e^(3/2), y=1-a e+sqrt(w)e^(3/2), g=1/2.
The exact pair survival is b2=1-a e/2. The right-normalized kernel is U=B(x,y,1/2) E(b2^-1), where the inverse is solely an algebraic normalization. Its physical source contains only the positive bigon and positive ordinary connectors.

Write kappa(r,s,j)=[z^(2j)](1+z)^r(1-z)^s. Then U=I+sum_(d>=1)e^d C_d(a,w), with the following ALL-ARITY operator formula:

C_d(a,w) = sum_(j=0..floor(d/3)) a^(d-3j) w^j H_(d,j),

H_(d,j) = (-1)^(d-j) sum_(l=0..d-3j) 2^(-l)
            sum_(r+s=d-j-l) kappa(r,s,j) M_(r,s) binom(Q,l).

Derivation: expand each arm as (I+delta_x)^(-Q_L) and (I+delta_y)^(-Q_R). In a term with r+s=k, choosing 2j asymmetric factors gives e^(k+j), a^(k-2j)w^j, sign (-1)^k and the displayed kappa. Odd asymmetric powers cancel because arm exchange gives M_(r,s)=M_(s,r). Multiply on the RIGHT by E(b2^-1)=(1-a e/2)^Q. Choosing degree l in that factor contributes (-a/2)^l binom(Q,l). Thus k+j+l=d and k>=2j, giving exactly the summation bounds and sign. At each fixed degree the sums are finite; on each fixed cap the operator binomial series is a valid formal identity (and agrees with the analytic source near e=0).

The accepted cubic provider gives C1=C2=0 and C3=r R3, with r=3w/8-a^3/16. In adapted coordinates (a,r), w=(8/3)r+a^3/6 and the physical leading domain is a>0, r>-a^3/16. In particular

C4=a^4 A4+a r B4,
C5=a^5 A5+a^2 r B5,

where A4=H_(4,0)+H_(4,1)/6, B4=(8/3)H_(4,1), and analogously A5,B5. These are universal source operators, not a claimed classification of every legal weak family or a proof that their positive cones are balanced. For caps containing the nine-root component, the accepted functional applied to that component has Phi(A5)=0 and Phi(B5)=84; that finite functional identity is not promoted to an all-cap rank statement.

## Coherent word equations, with shared variables

Fix one finite architecture with strictly ordered leading positions inside a fixed positive ordinary target interval. Let x collect ALL leading cell parameters and positions. Its exact normalized response has expansion

W(e,x) E(-tau)-I = e^3 F3(x)+e^4 F4(x)+e^5 F5(x)+e^6 F6(x)+... .

F6 here includes chronological cubic-pair products. No parameter is chosen separately by forest coordinate. For x(e)=x0+e x1+e^2 x2+e^3 x3+..., the first four equations are

F3(x0)=0,
DF3 x1+F4=0,
DF3 x2+(1/2)D^2F3[x1,x1]+DF4 x1+F5=0,
DF3 x3+D^2F3[x1,x2]+(1/6)D^3F3[x1,x1,x1]
 +DF4 x2+(1/2)D^2F4[x1,x1]+DF5 x1+F6=0.

All undenoted evaluations are at x0. These are FULL forest-vector equations. For caps containing the nine-root component, apply Phi to that component. Since Phi F3 and Phi F4 vanish identically for the specified family, the last equation projects to

D(Phi F5) x1+Phi F6=0.

Changing a at fixed r leaves the entire F3 unchanged. It changes Phi F5 by 168 a r exp(-30s) da for that cell. Nevertheless x1 must solve the second full equation and allow the third full equation to be solved. In particular the class of DF4 x1 modulo im DF3 is a real constraint. A nonzero derivative of one scalar is therefore not an independent correction mechanism.

## Exact existence transfer, only after an all-orders solution

For any FIXED finite architecture and copy cap, the original full-forest compiler gives finitely many polynomial equalities in the SAME survival/coin variables, with target parameters as fixed real constants. Suppose these equations admit an exact all-orders solution in real formal power series (or in a fixed Puiseux extension), and each required strict inequality has a strictly positive leading germ. The solution is a witness in an ordered Laurent-series field. Embed that field in a real closure, preserving the embedded real target constants. The finite existential formula transfers back to the real numbers by the standard model completeness of real closed fields. This supplies one actual finite strict source with the exact capped response.

No analytic convergence is needed for this existence implication. A convergent arc with prescribed jets is a stronger conclusion, for which approximation results could be used separately. The architecture must be fixed across ALL orders. Finite-order cancellation, or architectures whose lengths grow with truncation order, does not meet this premise.

## Remaining direct obligation

The formulas expose the actual coupled hierarchy; they do not solve it. The missing step is an all-arity, grade-compatible construction showing that one finite architecture per cap supports a coherent formal solution with strict germs, or a genuine obstruction to that construction. The broader original G4 may also be resolved by a different fixed-target/full-menu counterexample or a source-faithful finite-forcing theorem. None follows from this reduction.
