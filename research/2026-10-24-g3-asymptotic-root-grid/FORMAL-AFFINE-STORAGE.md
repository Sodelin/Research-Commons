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
cells have the additional jump terms. Their uniform source-specific bounds,
chronological cancellation, and the AG-Pair index estimate are UNPROVED.
The original nonzero raw storage boundary is not discarded. In particular
this identity supplies no V_h bound, finite positive replacement, all-input
witness bound, terminating NO or source-complete impossibility.

Existing next action: use these complete identities only when deriving actual
source estimates under the unchanged SAME-pair capped commutator. Do not
rerun the old special check or count the present algebra as a solved index
problem. All original owners, no-local-Git/no-worker rules and holds persist.
