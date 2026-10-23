> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Source concentration and exact closure on the paired cubic face

22 October2026. HAND/self-audited candidate, UNREVIEWED/UNCOMPILED.
Original all-input G3 remains OPEN. The word grammar and source scope below
are essential; this is not an arbitrary-core or INDEPENDENT-only theorem.

## 1. Prior-solution gate and the precise addition

Use the actual fresh private grammar

    W=E(z) B(x1,y1,p1) E(a1) ... B(xN,yN,pN) E(aN),

with every natural parameter strict, fresh bit IDs at distinct occurrences,
one tuple for COMMON/I, and opaque current-root grafting. Parent0 has
probability p; native gamma=1-p. A protected z remains a static source field.

The complete closest predecessor was reread:
G3-PAIRED-CAP3-COUPLED-LOWER-BOUNDARY.md,7228B/SHA256
fa989e2d5914c7241bd810ede95a638cf304de84ecdc280c78fe702aefd8977b.
It ALREADY proves the lower cubic inequality, the local square identity,
supermultiplicativity, and exact finite equality => at most one strict cell.
Its exact cap-three face constructor and existing controls are REUSE.
The complete mixed-triple successor d3a225493137b150245d565d6297882acca2cbb6e716aa618f08f7fbc7cd407d
supplies a separate necessary inequality, not a closure classification.

The later complete G3-PAIRED-GAP-ORDINARY-TUBE.md,13423B/SHA256
4e4fd3e29bd0f4ce1c94fa2ba3880e24cc345d2814c54f3aa28ab3b6d15edef6,
supplies the new all-cap full-kernel estimate used here. Its finite zero-gap
rigidity was explicitly credited as old. Neither of those inspected bodies
classifies the positive-gap cubic face of the entire word-image closure.
A bounded current-G3 source search found no existing concentration/face
collapse note; that is not corpus-wide absence or historical-priority evidence.

The old chronology diagnostic actually reread in COMPLETE Section6 is at
Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6,
research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-complete-classification/
attempt-7-inside-common-face/COMPLETE-PAIRED-WITNESS-ATTEMPT-AND-FATAL-EXACT-GATE.md,
SHA256db6d9a0ed4b3b18bf6437de7ff55a57cb8a4738db735319a1eeea5600aed2600.
Its W1/W2 cap-four separation is OLD and is not rerun. It explicitly does
not conclude an all-word finite-input NO. Section6 and that exact limitation
are the relevant read scope, not a new complete review of the whole attempt.

New claims relative to those suppliers: a word-length-uniform concentration
estimate; a complete finite-parameter description of the full paired closure
on the positive cubic face, valid at any finite cap; and a stronger fixed-z
all-word exclusion using the OLD separating words. Exact finite-face
membership itself is an integration of the OLD one-cell bound with RCF.

## 2. Scalar notation and reused source inequality

For a whole word let C,Q be COMMON/I pair no-merger survivals, and let T be
I three-root no-merger survival. Set

    P(C,Q)=3 C Q^2-3 C^2 Q+C^3,
    r=Q/C,  f(r)=3r^2-3r+1,
    kappa=T/C^3-f(r)=(T-P(C,Q))/C^3 >=0.

These are internal source-kernel coordinates. A legal observation caller
must actually recover them; notation supplies no hidden observation.

For bare cell i write c_i,q_i,t_i for its two pair values and I triple.
The OLD identities give

    r_i=q_i/c_i>1,  w_i=t_i/c_i^3>=f(r_i),
    r=product_i r_i,  T/C^3=product_i w_i,
    f(s)f(t)-f(st)=3(s-1)(t-1)(2st-s-t).                   (1)

Ordinary edges cancel from these ratios. Normalizing scalar products does
not commute or discard any actual forest matrix factor.

## 3. A uniform concentration estimate

Put A=log r and a_i=log r_i. When A>0 let M=max_i a_i and eta=A-M.
Then

    kappa >= 6 min(A/4, eta/2)^3.                         (2)

Proof. If eta=0 the assertion is the old nonnegativity. Otherwise set
delta=min(A/4,eta/2)>0. Add a_i in their original order until the sum first
reaches delta. The preceding sum was below delta and each a_i<=M=A-eta.
The selected sum is therefore in[delta,A-delta]. Its complement has the
same lower bound. If S,T are the products of the corresponding r_i,
S,T>=exp(delta), ST=r. Applying(1) inside the two scalar subsets gives

    kappa >= f(S)f(T)-f(ST)
      =3(S-1)(T-1)(2ST-S-T) >=6 delta^3,

using exp(delta)-1>=delta and
2ST-S-T=(S-1)+(T-1)+2(S-1)(T-1). This proves(2).
The partition only groups scalar ratios; no physical reordering occurs.

In particular if

    kappa < 6[(r-1)/(4r)]^3,

then log r>=(r-1)/r implies

    eta <= 2(kappa/6)^(1/3).                             (3)

For ANY sequence with r->r_*>1 and kappa->0, a single selected cell
therefore carries asymptotically the entire log ratio: its r_i->r_* and
the product of all other ratios tends to1. The number of other cells is
unrestricted. Bounding only the largest cell against its complement would
miss the case where every individual a_i is tiny; the greedy partition is
what excludes that case.

## 4. One actual physical macro, simultaneously at every finite cap

Let i maximize a_i and split the actual word as W=P0 B_i S0, putting the
connector immediately after B_i into S0. Let U=d_C(P0), V=d_C(S0).
The two residual log ratios are nonnegative and sum to eta. The paired
ordinary-tube supplier bounds their mode-specific deviations by L_m times
those respective log ratios.

The old E_m(s) is a matrix polynomial. Choose a total computable rational
J_m bounding its derivative row-sum norm on[0,1]. For either residual word,
its I pair q and C pair c obey

    q-c=q(1-exp(-log(q/c))) <=log(q/c).

Thus its I kernel differs from the SAME ordinary E(c) by at most
(L_m+J_m)log(q/c); the C kernel obeys the same conservative bound. Stochastic
telescoping around the retained ACTUAL B_i yields, in BOTH modes,

    ||K_mu(W)-E_m(U) B_mu,m(x_i,y_i,p_i) E_m(V)||
        <=(L_m+J_m) eta.                                 (4)

The chosen cell and U,V use the original tuple and pair coordinates only;
they do not depend on m. With free leading edge, U,V and that cell are
strict, so this is ONE actual strict one-cell word. Its COMMON pair C is
preserved exactly. Other observations, including its I pair, are only
approximated; no exact correction theorem is asserted.

With protected z, U<=z. Formula(4) instead has the canonical interpretation
E(z) E(U/z) B_i E(V). The added ordinary prefix cannot silently replace the
protected leading E(z). This macro has a finite CLOSED-cell representation,
and a strict approximation, but is not automatically a strict one-cell
word in the fixed-z grammar. Equations(3),(4) are a quantitative bound for
all word lengths and caps, not a ladder of cap-specific calculations.

## 5. Exact full-kernel closure on the positive cubic face

Fix m>=3 and a protected z in(0,1). Let S_m,z be the entire strict word
image in the paired full-forest carrier through m. Consider the face

    F={0<C<Q<1, T=P(C,Q)}.

Then cl(S_m,z) intersect F is EXACTLY the following finite polynomial image:

    K_mu=E_m(z) E_m(u) B_mu,m(x,y,p) E_m(v),
    u,v,x,y,p in[0,1],
    p(1-x)=(1-p)(1-y),

with the displayed positive-gap face conditions on its output.             (5)

Necessity. Choose actual words approaching a point of this face. For large
indices their ratios stay above1 and kappa tends to0. Select the maximizing
cell using Section3. Extract one subsequence along which its three physical
parameters and the two residual COMMON survivals converge. Positive C of
the limit bounds each residual survival and the selected c_i away from0.
Equation(4) sends both residual kernels to the SAME ordinary populations.
The prefix limit is z*u. No bound on the number of residual cells is used.

Let w_i be the selected cell's normalized triple. Every other normalized
factor is>=1, so f(r_i)<=w_i<=T_word/C_word^3. Both extremes tend to f(r_*).
The selected cell's OLD square defect therefore tends to0. In the limit
its c>0 and q>c, so p(1-p)>0. The identity

    t-P(c,q)=3p(1-p)c[p(1-x)-(1-p)(1-y)]^2

forces precisely the balanced-loss equation in(5). Matrix polynomial
continuity proves its full-kernel representation.

Sufficiency. Each parameter tuple in(5) is a limit of STRICT canonical
words with z retained. Represent E(u) as the closed cell B(u,u,0)E(1),
then append the cell B(x,y,p)E(v). Approaching its closed coordinates by
strict ones gives at most TWO strict cells and the desired limit. Their
output need not lie exactly on F before taking the limit. Balance and the
old cubic identity put the limit on F. This proves equality in(5).

With an unprotected leading edge the two ordinary prefixes combine, so one
closed cell suffices. With protected z, two closed cells suffice. The SAME
finite tuple works at all caps for any coherent all-cap limit: compactness
is taken in these five scalar parameters, and(4) then applies to every
fixed m. No infinite physical source is introduced.
Equivalently, writing S_m,z^(<=b) for actual strict words of at most b cells,

    cl(S_m,z) intersect F = cl(S_m,z^(<=2)) intersect F,
       S_m,z  intersect F =     S_m,z^(<=1)  intersect F.

The first identity is the new exact closure bound on this entire stratum;
the second is the OLD finite equality bound. Neither is a full-input H.

Do not exchange cl(S) intersect F with cl(S intersect F). Every strict
exact-face word has at most one cell by the OLD theorem. A protected field
can make the first set strictly larger, as the concrete example below shows.

## 6. Finite algebraic decisions and input-defined acquisition

For an algebraic full paired target ON F, exact strict membership is a
finite one-cell RCF formula with x,y,p,a strict and the actual old z/ties:

    K_mu=E_m(z) B_mu,m(x,y,p) E_m(a),
    p(1-x)=(1-p)(1-y).

This decision is REUSE/INTEGRATION of the old finite equality bound, not a
new all-length argument. Closure membership is now the finite closed
polynomial formula(5). Together these distinguish strict attainment,
nonattained closure and closure exclusion on this face. Off this face the
procedure returns UNRESOLVED, not an invented NO. No RCF run is claimed.

In an original finite core catalogue this face need not be an extra input
promise. Build a finite semialgebraic OUTER state fibre Omega_c(p) from the
actual joint compiler, static strict domain and proved slot invariants.
One explicit choice uses theta in D_c, nonnegative stochastic kernel blocks,
their actual two-/three-root entry projections, 0<C_s<=Q_s<=z_s<1,
T_s>=P(C_s,Q_s), the paired ordinary tubes, and F_c(theta,K)=p.
Unprotected z_s is an existential initialization variable; a protected z_s
retains all its original static relations. Arbitrary synthetic blocks are
allowed only in this OUTER test and are never returned as sources.
It must contain every actual source state, with each slot's paired pair/
triple coordinates retained internally. Test by RCF whether Omega_c(p)
allows ANY slot with T_s>P(C_s,Q_s). If FALSE, every actual fitting word
of that template has at most one cell per slot; the exact old source grammar
can then be tested at those finite counts. If the outer fibre is empty it
already excludes that template. If off-face states remain possible, this
branch supplies no global NO for that template.

Only when EVERY alternative template is excluded may an original all-core
NO be returned. A bounded exact witness remains valid regardless of other
templates. The acquisition predicate is finite and input-derived, but no
claim that it covers all inputs is made. Auxiliary unobserved mode kernels
are internal necessities of the same tuple, never extra user queries.
The old whole-fibre/provider obligations are not assumed without this
actual sound outer-fibre test. No generic factory or new execution backend
is selected here.

## 7. A stronger fixed-field NO from an OLD chronology separator

The reused Section6 source gives

    W1=E(1/2) B(1/2,1/2,1/2) E(1/4),
    W2=E(1/4) B(1/2,1/2,1/2) E(1/2),

and proves that their full cap-four kernels differ despite all their
paired no-merger products agreeing. Its captured quotient values are

    (c4,h4)(W1)=(1/24576,1/8192),
    (c4,h4)(W2)=(1/786432,1/786432).

These separation values and their source attribution are OLD, not a new
producer execution or a newly licensed observable.

Now fix the declared canonical leading field z=1/2 and use the complete
paired cap-four kernel of W2 as target. Its scalar coordinates are

    C=1/16, D_C=1/4096=C^3,
    Q=3/32, T=13/16384=P(C,Q).

ANY finite strict fitting word must have exactly ONE cell, by the old cubic
face theorem. The COMMON Jensen equality forces equal arms. The local
square equality then forces p=1/2. The ordinary-bank product is
A=2Q-C=1/8, and the arm survival is C/A=1/2. Protected z=1/2 forces its
connector to be a=A/z=1/4. Thus the ONLY possible paired full-kernel
candidate is W1, already separated from W2 at cap4. NO finite strict word
in this fixed-z grammar fits the target. This excludes every length,
not merely two candidate words or a numerical range of lengths.
The same conclusion excludes a limit of exact-face one-cell words: compact
one-cell parameters at this positive-gap target have p in(0,1), and the
same target equations force their limit to the interior tuple of W1.
Consequently W2 is outside cl(S_m,z intersect F), not just outside S_m,z.

Nevertheless the target lies in its actual paired closure, at EVERY cap.
For n>=3 put

    p_n=1-1/n, a_n=1-1/n, b_n=1/[2(1-1/n)],
    V_n=E(1/2) B(1/2,1/2,p_n) E(a_n)
                       B(1/2,1/2,1/2) E(b_n).

Each V_n is strict and retains the leading field exactly. Its entire
COMMON law is EXACTLY E(1/16). Polynomial continuity gives its paired full
law -> that of W2. If v_n=p_n(1-p_n), its scalar values are

    C_n=1/16, D_n=C_n^3,
    Q_n=(3/32)(1+2v_n),
    T_n=(13/16384)(1+9v_n),
    kappa_n=(9/4)v_n(5-12v_n)>0.

Thus these are off-cubic-face strict approximants, even though they stay
on the EXACT COMMON ordinary-clock fibre. The leading-field distinction
cannot be repaired by a compact boundary tuple or by more strict cells.
If z is free, W2 itself is a strict one-cell YES, so the protected-field
hypothesis cannot be discarded.

This is a mathematical private-interface NO with an effectively specified
rational full-kernel target, using the retained compiler expression for W2.
No expanded native response packet or original Source/Calendar/Code execution
is claimed. Original legal completion transfer still needs its supplied
faithful decoder; arbitrary other original cores, weaker channels or a
different unfixed exterior are not excluded by this private argument.

## 8. Remaining original goal

The new source concentration/closure result handles a complete algebraic
stratum, with retained chronology and a genuine protected-field obstruction.
It is not a total one-witness H, invariant completeness, general positive-gap
attainment or the rank-five log-purity zero test. It does not answer original
I-only G4 or construct a fixed-target exact-rival family. All owners, native
writer/controller UNBOUND, old held/USED/UNKNOWN history, no-local-Git and
no-subagent restrictions remain. The next master work must still handle
the other exact fibres without turning this face into the entire goal.

## 9. Actual bounded control and acceptance scope

check_cubic_face_collapse.py was executed ONCE and passed. It checks seven
rational-weight greedy partitions, four scalar-ratio product cases (including
a many-small-factors guard against the largest-only proof), the complete new
polynomial kappa(v) identity, the fixed-field uniqueness arithmetic and four
strict off-face approximants. The old W1/W2 separation values are consumed
from their SHA-authenticated immutable source; their producer is NOT rerun.
Only helper definitions from the preceding exact polynomial checker are
loaded after a byte-hash check; its main and old controls are NOT called.

Full source/results encrypted before first runtime persistence:
[encrypted runtime receipt retained privately], ciphertext SHA256
ff0279a703d7ca5c2e10d712c22691146c91abc5451abb4514022f9476e99fd5.
These finite arithmetic and captured-data consumers are not execution or
independent acceptance of the arbitrary-real concentration proof, closure
classification, all-length NO, original decoder or full original G3 algorithm.
No RCF/source compiler/Code/Calendar/native/Lake/model job, held replay,
peer dispatch, new chat/subagent or local Git mutation occurred.
