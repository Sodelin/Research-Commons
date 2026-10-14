# Hand review: bounded pair-clock isotropic energy obstruction

Reviewer: Codex whole-source lane, 14 October 2026.

Status: SCOPED HAND ACCEPT of
[FIXED-CLOCK-DIAGONAL-VANISHING-C1-ENERGY-OBSTRUCTION-SOL.md](FIXED-CLOCK-DIAGONAL-VANISHING-C1-ENERGY-OBSTRUCTION-SOL.md),
SHA256 `47bc01028dd7719fc4f6c67951a1409b3cd0ce1985ad48b22cb2fc54f637843b`.
The unrestricted-state C1 result and separate actual-prefix quadratic
supplement both pass at their stated scopes. This note reviews the lead G4
researcher's proposed extension and Sol's written proof independently of
the earlier quadratic proof.

## Actual source and budget

Fix a finite cap m>=9 and positive total pair-hazard budget H. The diagonal
state here is finite: it may include every b_2,...,b_m and therefore the
elapsed pair hazard. It is not the entire infinite diagonal sequence.

The inherited full-rank ordinary-diagonal theorem supplies a strict finite
word C_0 at an arbitrarily small positive hazard, say H/8, with zero higher
Newton defects and surjective defect differential. A continuous local
physical parameter section C_eta therefore realizes every sufficiently
small defect eta. Shrinking its neighborhood preserves all strict source
parameters and bounds its hazard by H/4. This is an open image of one finite
source chart; no signed factors or external mixtures are introduced.

The inherited exact f-zero arc has actual parameters

    x=1/2, y=exp(-u z_sigma(u)), g=u,
    f=0, -h+2e=6 W_sigma u^4+O(u^5), W_sigma!=0.

For sufficiently small u>0, both arms and the inheritance parameter are
strict and the displayed lower entry is nonzero. Every finite diagonal
tends to one, so the higher defect tends to zero and the pair hazard tends
to zero. Its first arm remains of length log 2: small pair hazard is not
being equated with small total physical arm exposure or calendar duration.

Choose u so that its defect delta can be cancelled by C_(-delta) and its
hazard is below H/4. The two words together have zero higher defects and
hazard below H/2. Positive ordinary pads can fill the remaining hazard
exactly to H while supplying every required leading, separating and final
ordinary passage. The exact endpoint diagonals are those of E_H. Pair
hazards add and are nonnegative, so every intermediate prefix stays within
the stated budget. All statements concern one physical tuple per word.

## Energy contradiction

Write the tested energy as

    F=v+P_d(a,b)+Phi(d),

where P_d is C1 at the origin, its gradient there vanishes, and
P_d(r,r)=0 for all r. In the inherited append recurrence, a bare cell maps
the virtual input (a,b)=(0,0) to (l,l), without changing v. An ordinary
append maps that virtual input to itself. Thus dissipation at this input
forces Phi(d_next)<=Phi(d) for every step of the actual diagonal path.
Normalization Phi(d(E_H))=Phi(d(I)) makes every decrement on the constructed
path zero. No continuity or differentiability of Phi is needed.

At the chosen f-zero cell, l=0 and the exact append gives

    a'=a, b'=k b,
    v'-v=s[(-h+2e)a+h b], s>0.

For these fixed actual diagonal states d,d_next, vanishing gradients imply
P_d(a,b)=o(norm(a,b)) and P_d_next(a,kb)=o(norm(a,b)). The constant potential
increment is already zero. Set b=0 and choose a of the sign of -h+2e.
For sufficiently small nonzero a the energy increment is strictly positive.
This contradicts dissipation even on a two-sided neighborhood of the
origin. No uniform differentiability over the diagonal states is needed:
the realizing positive u and its two states are fixed before a tends to zero.

## Separate actual-prefix supplement

Section 6 has the narrower hypothesis Phi=0 and locally bounded quadratic
coefficient c(d). Its two actual weak families have the asserted signs:
substitution of z=1/2 and z=1 into the inherited cubic coefficient gives
respectively f=epsilon^3/120+O(epsilon^4) and
f=-epsilon^3/24+O(epsilon^4). Both have strictly positive arms and interior
coins at every realizing epsilon. Either sign can therefore be chosen to
match the fixed nonzero e_0 of a sufficiently weak exact f-zero cell B_0.

For the actual prefix E_L U_epsilon E_epsilon, ordinary diagonal transport
gives exactly a=exp(-15L)f(U)/p_7(U), b=a exp(6 epsilon), and v=0.
After the fixed B_0 and a positive trailing E_epsilon, the increment of v is

    s_epsilon a[2e_0+h_0(exp(6 epsilon)-1)],
    s_epsilon -> exp(-15L)/p_(4,0)>0.

The trailing pad leaves normalized v unchanged, leaves a unchanged, and
multiplies b by exp(6 epsilon), as used in the candidate. Both the old and
new quadratic energy terms are O(a^2), since c is locally bounded at the
two limiting diagonal states and all displayed transport multipliers are
bounded. The leading linear contribution is strictly positive. Taking
L<H/4, the fixed B_0 with hazard<H/4, and sufficiently small epsilon keeps
both compared, fully padded strict words below the budget H.

This supplement consequently needs no virtual prefix and no diagonal
return. It does not claim ordinary endpoint matching, and does not extend
its estimate to arbitrary d-dependent differentiable P_d: that would need
uniform small-o control along the moving diagonal states. Local boundedness
of the quadratic c supplies exactly the control actually used here.

## Precise limitation and provider checks

The main C1 contradiction tests virtual upper coordinates near zero at an
actual diagonal prefix. It does not assert these coordinates are themselves
reachable prefixes with that diagonal. A certificate restricted to a proved
actual-prefix cone, a nonzero linear tangent, nonsmooth corrections, or
additional lower-state information is outside this result. Ordinary-append
dissipation and the stated endpoint normalization are both used. This is
not an exclusion of exact physical full-kernel returns or a G4 closure.
The separate supplement rules out actual-prefix rescue specifically for
the zero-potential, locally bounded isotropic quadratic template; it makes
no such assertion for all the preceding alternatives.

I directly reread and verified these supplier hashes:

- Full-rank ordinary diagonal return: `ab700065a7d0ed1a6ef5a680743ecffabdc24728325a1a58b70673d254c41905`.
- Exact strict f-zero arcs: `ec2ee928996f18c1f6481270eb1d54460b8044a800d6c5b14dae67d687bd9f0f`.
- Exact source-state append interface: `7da5c426153438a70513dc7bf703f5ab77630831d4196bd6e83f718c4f75470f`.
- Earlier quadratic reduction: `c032a131f1584f0dfeb45744877f625d65b50c1be1251b63c0de30e1ce67d9cc`.

This is a hand composition audit reusing those providers. I previously
reviewed related diagonal and source-transfer results, but did not author
the proposed energy extension. No new computation, source compiler, primary
literature search, Lean verification or Git operation was performed.
