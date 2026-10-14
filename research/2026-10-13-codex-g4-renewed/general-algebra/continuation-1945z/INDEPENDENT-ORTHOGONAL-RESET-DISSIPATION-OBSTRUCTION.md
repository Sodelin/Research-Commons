# A fixed Hilbert-space reset dissipation cannot retain the full source law

Contributor: Codex laplace_recovery lane, 14 October 2026.
**Hand-derived obstruction to a proposed general energy representation.**
The actual route/coalesce/forget factorization and completed-quartet formula
are inherited. No finite-cap scan, source execution, Lean proof, historical
priority, or general INDEPENDENT forcing/impossibility result is claimed.

## Purpose and exact conclusion

The sought positive INDEPENDENT certificate would need a finite nonlinear
source inequality controlling arbitrarily many weak cells. The accepted
fair-parabolic chronological energy suggests trying an exact global
orthogonal-projection dissipation identity. This note checks one precise
version of that idea and finds an obstruction.

On the COMPLETE labelled-forest state space at any cap containing four
fresh roots, there is no fixed positive-definite inner product making both
ordinary coalescence and every actual independent-routing cell contractions.
Already one fair equal-arm cell with positive duration contradicts this.
Consequently no fixed positive-definite inner product on the corresponding
coloured forest space can make the routing-reset projection orthogonal
AND its coloured Kingman evolution contractive.

This is stronger than merely failing to symmetrize the generators: even
nonsymmetric dissipative generators are excluded at this interface. It
does not rule out an indefinite or time-dependent form, a nonlinear
endpoint functional, or a positive quotient that explicitly loses some
completed genealogy directions. Those alternatives need separate proofs.

## 1. A finite-dimensional contraction lemma

Let Q generate the ordinary finite labelled-forest process, retaining each
already formed rooted genealogy as an opaque current root. Use column
probability vectors. Let Z be the subspace spanned by all fully coalesced
one-root genealogies on this fixed label set. Ordinary evolution has

    P = lim_(s to infinity) exp(sQ),   P^2=P,
    range P = Z.

These are finite-state Kingman facts: transient states have at least two
roots and eventually coalesce, whereas each one-root genealogy is fixed.
Let B be any linear operator fixing Z pointwise.

**Lemma.** If exp(sQ) for every s>=0 and B are contractions in the SAME
positive-definite Hilbert norm, then

                         P B = P.                         (1)

Proof. The limit P is a contractive projection and is therefore the
orthogonal projection onto Z. To see the orthogonality directly, for
z in Z and y in ker P, contractivity gives
`||z|| <= ||z+t y||` for every real t, hence `<z,y>=0`.

For a contraction B fixing z, its adjoint is a contraction and
`<B* z,z>=<z,B z>=||z||^2`. Equality in Cauchy--Schwarz implies B* z=z.
Thus B preserves Z's orthogonal complement as well as Z. Applying the
orthogonal projection gives (1). QED.

In particular (1) says that applying B before ordinary infinite
completion cannot alter ANY completed labelled genealogy probability.
This is an equality of linear maps on the complete forest space, not a
claim only about the number of final roots.

## 2. An actual strict cell violates the consequence

Take one natural INDEPENDENT fair cell with equal positive arm duration
t>0, routing every current root independently, and write x=exp(-t).
The accepted exact completed-quartet formula is

    Pr_(B(t,t,1/2) Q)(total balanced quartet) - 1/3
                             = (1-x)^3/12 > 0.             (2)

Here Q denotes ordinary infinite completion in the probability notation;
as a column operator the left completed map is P B. Ordinary completion
alone gives balanced probability 1/3. A one-root genealogy passes through
B unchanged, so B fixes Z as required by the lemma. Equation (2) therefore
contradicts (1).

This gives the stated impossibility of a common positive-definite
contractive metric. It uses an exact strict source, not a boundary
parameter or a series approximation. For any larger cap, the same
four-label source quotient supplies the discrepancy; equivalently, work
on the invariant full forest block with those four original labels.

The formula (2) is inherited, not newly computed here. In the accepted
general formula with g=q=1/2 and u=v=(1-x)/2, the contrast is
`(2/3)[q u^3+g v^3-3gq(u-v)^2]=(1-x)^3/12`.

## 3. Consequence for literal orthogonal routing resets

Let F be the complete uncoloured forest space and C its coloured version.
At a fixed interior coin g, the exact physical maps are

    S_g : F -> C,   independent routing of every current root;
    R   : C -> F,   forget colours, preserve the rooted forest;
    R S_g = I;
    P_g=S_g R,      P_g^2=P_g.

Let G=a Q0+b Q1 be the coloured Kingman generator, with positive arm
coefficients a,b. The physical family is

                         B_t=R exp(tG) S_g.                (3)

Suppose a positive-definite inner product on C made P_g orthogonal and
exp(tG) contractive for every t>=0. Give F the induced norm
`||v||_F=||S_g v||_C`. It is positive-definite since RS_g=I.
Orthogonality of P_g implies that R is the adjoint of this isometric S_g.
Thus (3) is a contraction on F for every t>=0.

The first derivative is the exact source identity

              R G S_g = [g^2 a+(1-g)^2 b] Q = mu Q,
                            mu>0.                          (4)

Each unordered pair of current roots is together in colour 0 with
probability g^2 and colour 1 with probability (1-g)^2, giving (4), with
all opaque subtrees retained. Contractivity of B_t implies
`<v,mu Q v> <= 0` by differentiating `||B_t v||^2` at zero.
In finite dimension this dissipativity makes exp(sQ) contractive for all
s>=0 in the same induced norm. Section 1 now applies to every B_t.
For g=1/2 and a=b=1, Section 2 contradicts it for every t>0.

Equivalently, imposing the adjoint relation R=S_g* from the outset and
requiring G+G*<=0 leads to the same contradiction. Requiring G to be
self-adjoint is an even stronger impossible premise. The failure occurs
with a single fixed fair coin; varying coins and their weighted metrics
are not needed to produce it.

## 4. Semidefinite forms and the observation boundary

A positive SEMIDEFINITE form can evade positive definiteness only by
losing information. Suppose Q and B act contractively in its seminorm.
Its null space is invariant, so both maps descend to contractions on the
Hilbert quotient. The proof of Section 1 gives

                       (P B-P)F subset ker M,              (5)

where M is the form's matrix. Hence every completed-topology discrepancy
created by B is invisible to that form. In particular the nonzero fair
quartet contrast direction in (2) must be null.

This does not exclude every useful semidefinite source representation.
It states the exact price of this fixed-metric approach. An attempted
full-observation argument must prove that the discarded directions are
irrelevant to its promised conclusion; it cannot declare the quotient
faithful after erasing them. A form on the separate 9-to-4 spectral
projection need not retain all absorbing genealogy directions and is
not itself refuted by (5).

## 5. What remains missing for a genuine positive guard

The accepted chronological Green energy is an ordered endpoint identity
after specific horizontal moment cancellation. It is not claimed to arise
from the constant contractive metric just excluded. Its fair-parabolic
scope therefore remains intact.

For arbitrary cells the exact spectral update contains the separate
source coordinates f,h,e and, in particular, the term

                    V' = V p4+(Y-X)h+2X e.

A global positive guard must control these source-coupled terms and the
changing ordinary transports, rather than replace them with a universal
orthogonal reset variance. Time-dependent metrics would also introduce
their own derivative/boundary terms; no sign for those terms is supplied
here. A quadratic endpoint expression may still be possible, but its
nonnegativity and equality case require an actual-source argument.

No such general endpoint inequality was established in this attempt.
The exact obstruction above prevents one plausible but unjustified lift
of the known asymptotic energy. It does not show a positive lower bound
for an exact-return threshold, prove finite INDEPENDENT forcing, or supply
an exact fixed-target all-prefix rival.

## Inherited evidence and reuse

- [Actual source lift](../../../2026-10-08-dot-g4-positive-composition-attempt-1702z/POSITIVE-COMPOSITION-CUBATURE-AND-SOURCE-LIFT-FAILURE.md),
  Section 3: equations (3)--(4) use its exact current-root coloured model.
- [Original completed-quartet/source transfer](../../../2026-10-06-dot-g3-original-quartet-whole-fibre-no-0454z/PROOF.md),
  Sections 2--3: original cut-child marginal and exact quartet formula.
- [Accepted ordered Green energy](../../../2026-10-08-dot-g4-fair-energy-hazard-1220z/ORDERED-GREEN-ENERGY-SEPARATED-FAIR-SOURCE-R1.md):
  nonlinear chronology obstruction at its stated asymptotic scope.
- [Exact operation-closed source state](../../../2026-10-07-dot-g4-coupled-source-state-interface-0252z/METHOD-COMPARISON-AND-SOURCE-STATE.md):
  full physical append update and the unremoved e term.

The elementary Hilbert contraction lemma and its application above are
hand arguments. No primary-literature novelty claim is made. The next
substantive positive route must either derive the actual ordered nonlinear
source inequality with a count-independent equality case, or replace
that approach; constant-metric projection dissipation is not that proof.
