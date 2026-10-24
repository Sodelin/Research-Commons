> Current successor —24October2026: [COMPENSATED-SOURCE-JUMPS.md](COMPENSATED-SOURCE-JUMPS.md)
> now PROVES uniform all-coin source-jump bounds and a horizontal compensation
> with residual reference forcing O(h^6). Signed accumulated coercivity,
> V_h and the original index/termination claim remain UNPROVED.
> The8059B body below follows UNCHANGED from980c2d0e; its older missing-
> source-bounds wording is historical, not the current open frontier.

# General affine-storage identities — algebra verified

Stable key: G3-FORMAL-AFFINE-STORAGE-01. Authored24October2026UTC.
Status: PROVED by elementary algebra at the scope below; one exact formal
coefficient check passed. Independent review and Lean are separate and absent.
This supplies no source coercivity, inferred index or original G3 endpoint.

## Exact scope and predecessor

The earlier G4 count-uniform storage check, source
count_uniform_storage_identity.py,2967B/SHA256
a7d6a1b22972a35b45719359671f79495c16a65feedbc5451f44a565b46cfda5,
checks the special jump with equal top entries, no central entry and no
affine correction. That result is reused, not reopened. The present identity
retains unequal top entries, a central entry and two affine terms, as required
after a reference eigenbasis change. It is a general algebraic identity,
not a new biological source formula or a full attack.

Let d1 be invertible, and set

    Phi=z-(kappa/2)(b^2-a^2)+la*a+lb*b,
    a+=(d2*a+x)/d1,
    b+=(d3*b+y)/d1,
    z+=(d4*z+u*a+t*b+v)/d1.

Then Phi+=(d4/d1)Phi+err, where EXACTLY

    d1^2*err =
      (kappa/2)*[(d4*d1-d3^2)*b^2-(d4*d1-d2^2)*a^2]
      +[d1*u+kappa*d2*x+la*d1*(d2-d4)]*a
      +[d1*t-kappa*d3*y+lb*d1*(d3-d4)]*b
      +d1*v-(kappa/2)*(y^2-x^2)+d1*(la*x+lb*y).

For constant coefficients and the differential equations

    a'=15a+q12, b'=21b+q13,
    z'=30z+q24*a+q34*b+q14,

one has EXACTLY

    Phi'-30Phi =
      -6*kappa*b^2
      +(q24+kappa*q12-15la)*a
      +(q34-kappa*q13-9lb)*b
      +q14+la*q12+lb*q13.

For example, choosing la=(q24+kappa*q12)/15 and
lb=(q34-kappa*q13)/9 cancels the linear terms. Neither the sign nor the
source-specific asymptotic size of the remaining constant follows.

Proof: substitute the three affine numerators into Phi+, multiply by d1^2
and expand the two squares. Collect the a^2,b^2,a,b and constant terms.
For the drift, apply the chain rule and subtract30Phi. The a^2 term cancels
and the b^2 coefficient is -21kappa+15kappa=-6kappa. These operations prove
both identities over the rational polynomial ring, hence at every permitted
specialization. No physical sign, independence or source premise is used.

## Actual bounded verification

The accompanying6539B script, SHA256
c2654bae2e0a7a61a9ee201a9d827bba116c54286f000b8bd1a48ee30345bcfc,
reuses exactly EIGHT unchanged sparse rational-polynomial helper functions
from the predecessor through AST selection. Its old main is not executed.
All20 variables are formal indeterminates; no physical tuple, source law,
copy count, empirical model, solver or research compiler is evaluated.

Action G3-FORMAL-AFFINE-STORAGE-20261024/revision1 executed ONCE.
The complete coefficient residuals for both identities are identically zero.
Two controls that omit the central-entry term or unequal-square term both
have nonzero residuals and are rejected. Actual status:
PASS_UNIVERSAL_FORMAL_AFFINE_STORAGE, exit0. This is exact rational
polynomial arithmetic, not a numerical fit or Lean/kernel check.

Intent and full result were encrypted before their first persistence with the
existing one-identity record writer. No private runtime payload is published.
No original scientific model/source producer or old main/suite was replayed.
The actual user model-testing and held/native/controller restrictions remain;
a prior blanket hand-only/no-symbolic continuation was a self-selected plan,
not a new user stop. This one generic check does not release any other hold.

## What is still missing

A commuting endpoint may become diagonal in the reference basis, but the
ordinary evolution then has the displayed forcing and actual conjugated
cells have the additional jump terms. The arbitrary-source jump/error estimates,
chronological cancellation, and the AG-Pair index estimate are UNPROVED.
The original nonzero raw storage boundary is not discarded. In particular
this identity supplies no V_h bound, finite positive replacement, all-input
witness bound, terminating NO or source-complete impossibility.

Existing next action: use these complete identities only when deriving actual
source estimates under the unchanged SAME-pair capped commutator. Do not
rerun the old special check or count the present algebra as a solved index
problem. All original owners, no-local-Git/no-worker rules and holds persist.

## Reference forcing addendum — PROVED by hand from OLD source jets

This is a derived coordinate calculation, not a new bare-source coefficient
or a uniform arbitrary-word estimate. It was not executed by the preceding
formal-polynomial check. Independent review/Lean remain absent.

Use the OLD actual multiplicative9/7/6/4 representation with ordinary
generator D=diag(-36,-21,-15,-6), and kappa=5/3. For the SAME active

    S(t)=E(t) B_I(t/(2-t),t/(2-t),1/2) E(t^2*(2-t)),
    h=-log(t),

write its represented matrix as

    R(S)=[ s1 X Y 0 ]
         [ 0 s2 0 U ]
         [ 0 0 s3 T ]
         [ 0 0 0 s4 ].

The zero14 entry is exact: a single bare cell has zero14 and the two
ordinary bookends are diagonal in this representation. OLD fair-source
jets give, with f0=1/15,

    (s1,s2,s3,s4)=1-3h*(36,21,15,6)+O(h^2),
    X=f0*h^3+O(h^4), Y=f0*h^3+O(h^4),
    U=-kappa*f0*h^3+O(h^4),
    T= kappa*f0*h^3+O(h^4).

Here the actual arm exposure is log(2*exp(h)-1)=2h+O(h^2).
The retained fair cubic rule f=mu^3/15+O(mu^4), mu=arm/2,
therefore applies. Multiplying by the two actual diagonal bookends changes
none of the displayed leading cubic coefficients. The first-order diagonal
clock3h is the already proved actual reference pair clock.

For sufficiently small h>0 all four diagonal values are distinct. Its
EXACT eigenvector matrix is

    P=[ 1 A B G ]
      [ 0 1 0 D0]
      [ 0 0 1 E0]
      [ 0 0 0 1 ],

    A=X/(s2-s1), B=Y/(s3-s1),
    D0=U/(s4-s2), E0=T/(s4-s3),
    G=(X*D0+Y*E0)/(s4-s1).

Direct substitution gives R(S)*P=P*diag(s1,s2,s3,s4); no spectral
eigenvalue of an UNKNOWN word has been substituted here. The four
denominator gaps have nonzero linear terms. Thus the ratios extend
analytically to h=0 and the reused jets yield

    A= h^2/675+O(h^3),       B= h^2/945+O(h^3),
    D0=-kappa*h^2/675+O(h^3),
    E0= kappa*h^2/405+O(h^3),
    G= kappa*h^4/1366875+O(h^5).

The ordinary generator in this basis is P^-1*D*P. Its actual off-diagonal
coefficients, in the notation of the generic drift above, are EXACTLY

    q12=-15A, q13=-21B, q24=-15D0, q34=-9E0,
    q14=-30G+15A*D0+9B*E0.

Choose the affine correction that removes the two linear drift terms:

    la=(q24+kappa*q12)/15=-D0-kappa*A,
    lb=(q34-kappa*q13)/9=-E0+(7kappa/3)*B.

The leading h^2 terms cancel in BOTH, so la,lb=O(h^3). Consequently

    eta=q14+la*q12+lb*q13
       =kappa*h^4*(-30/1366875-15/455625+9/382725)+O(h^5)
       =-4*h^4/76545+O(h^5).

This proves eta<0 for all sufficiently small positive h. In particular
the forced drift is NOT the old homogeneous -6*kappa*b^2 drift, even
though a commuting whole endpoint becomes diagonal in this exact basis.
The coefficient has now been derived by hand; its earlier tentative
working label is superseded at precisely this reference-only scope.

This does not sign or bound the general conjugated jump errors. The
latter have the central/unequal-square/affine terms in the full identity.
One cannot absorb them, integrate a bound using the whole COMMON budget
as though it were only physical ordinary exposure, or infer V_h/index
from the sign of eta. No source count/coin margin, new observer, physical
inverse or altered reference is acquired.

Reused sources actually read: the12533B count-uniform compact proof,
SHA256fa6eb9f154fc35fa50d093b5037f9bf7dc6c754996299371db436436e62854a0,
Sections2--4 (complete body read); and the COMPLETE2753B retained fair
source-coefficient consumer, SHA256
6445cc6b81c92b4d0dbad9dada072d1e360e422cb704b7eba9ef3152be3586b9.
Its cubic rule and OLD representation are reused, not rerun or relabelled
new source discoveries. The older unpromoted reference-basis calculation
is the immediate predecessor. Historical novelty is not assessed.
