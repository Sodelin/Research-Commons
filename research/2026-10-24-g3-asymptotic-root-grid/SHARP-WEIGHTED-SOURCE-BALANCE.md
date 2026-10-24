# Sharp weighted source balance and action-controlled remainders

Stable key G3-SHARP-WEIGHTED-SOURCE-BALANCE-01.
Existing G3 owner,24October2026UTC. PROVED HAND at the displayed scopes;
author self-review complete. Independent review, Lean formalization and
source/tuple/coefficient execution have not been performed.

Original total G3 and AG-Pair remain UNPROVED. The new balance removes
controlled OFF-DIAGONAL prefix-state errors, while retaining the exact
signed constant source functional and the ACTUAL diagonal transports.
No action upper bound, endpoint decoder or integer phase is supplied.

## 1. Original assumptions and completed providers

Keep the original paired equal-arm COMPLETE-cap12 commutator, arbitrary
strict coins/scales/counts and one physical tuple across every row:

    K_COMMON=E(c), b2I(K)=c^(3/4), [K_I,S(t)]=0,
    H=-log c, h=-log t, 0<h<H/4.

Choose one fixed small budget before h. Original IDs, register, CURRENT
roots/opaque grafts, chronology, legal menu and all-core source transfer
remain unchanged. No extra observation or physical inverse is introduced.

Use the completed source variables

    C_i=exp(-tau_i Q)B_i, u_i=-log q_i,
    v_i=g_i(1-g_i), beta_i=(2g_i-1)^2,
    r_i=v_i*(beta_i*u_i^2+u_i^3),
    s_i=v_i*(beta_i^2*u_i^3+beta_i*u_i^4+u_i^5).

Write S_cost=sum s_i. Completed cap12 bounds are

    E_a+E_b<=C Hh^6, S_cost<=C Hh^4,
    sum r_i^2/u_i<=S_cost/2,
    sum u_i*((a_i-)^2+(b_i-)^2)<=C(E_a+E_b).        (1)

These are REUSE, not new energy/trace/source results:
RESONANT-ORDINARY-FORCING-ENERGY.md13183B/SHA
200bb6bab172bcb56a42bf2f95ab5d2f711a0e918b8edbf8be32056b970faceb,
and MATCHED-FULL-BAND-LINEAR-ABSORPTION.md12383B/SHA
5801efb496cf76f7a0259513bb334c12b9688645792d7a32b35861bbb696a8e1.

The exact jump/drift and source bounds are REUSE from
COMPENSATED-SOURCE-JUMPS.md14724B/SHA
794bcb58e93ed33c2075b6176c229875c7235a788e1c5609a3890e4f2dd6e0e0,
and QUADRATIC-STATE-ABSORPTION.md11831B/SHA
8dea255b64f1e7cf87962919125b217dc9d18d2be0c66bf9da62bb8a51dd7a74.
The relevant exact statements were reread before this write.

Retain the positive storage weight w, ordinary w'=-30w and source
w+=w-/delta, delta=d4/d9. It is the ACTUAL prefix k9/k4 ratio, so
0<w<=1 with a fixed positive lower bound. Put I=integral w.

## 2. Absolute prefix-state errors improve beyond order h^6

The old source jump is EXACTLY epsilon0+ell_i(a,b)+Q_i(a,b), with

    |ell_i(a,b)|<=C*(s_i+h^2*r_i)*(|a|+|b|),
    |Q_i(a,b)|<=C*r_i*(a^2+b^2).

The linear symbol ell_i here is not the pair-loss logarithm.

For u<=1, s<=C*u^3. Hence s^2/u<=C*s^(5/3), and(1) gives

    |sum w_i+ ell_i|
      <=C*sqrt(Hh^6)*sqrt(S_cost^(5/3)+h^4*S_cost)
      <=C*(H^(4/3)*h^(19/3)+Hh^7).                (2)

There is no division by an energy or a rare coin.

For the quadratic term, write r/u=v*beta*u+v*u^2. Since

    (v*beta*u)^3<=v^2*beta*s<=C*s,
    (v*u^2)^(5/2)<=v^(3/2)*s<=C*s,

and s<=S_cost<=1 on the fixed domain,

    max_i r_i/u_i<=C*S_cost^(1/3).

Thus the OWN-PRECEDING trace in(1) gives

    |sum w_i+ Q_i|<=C*H^(4/3)*h^(22/3).            (3)

This is an absolute error, stronger than the older epsilon-energy
absorption. The older theorem is unchanged, not reopened.

## 3. The exact weighted constant-source balance

Use the old reference entries A=A_h,B=B_h,Theta(h), kappa=5/3.
Let c30=G30(S)/(s9-s12), Omega=4c30/3+A-7B/3, as in the completed
resonant theorem. Source ratios are

    alpha=d7/d9, gamma=d6/d9,
    delta=d4/d9, delta_z=d9/d12.

Keep the normalized full12-to9 driver G30(C), not A12(K) on a word.
Define the following function of ONE actual source and the known h:

    K_h(C)= B*(1-gamma)/9-A*(1-alpha)/15
             +(2/45)*[F/d9-G30(C)/d12-c30*(1-delta_z)].

Let epsilon0_h(C) be the EXACT old constant jump. Explicitly, with
X,Y,V the actual entries of P_h^(-1)C P_h and
La=-D_h-kappa*A+2kappa*B, Lb=-E_h-kappa*B,

    epsilon0_h(C)=(V+La*X+Lb*Y)/d9
                       -(kappa/2)*(Y^2-X^2)/d9^2.

All entries come from that SAME source. They are not independent controls.
Put

    Gamma_h(C)=epsilon0_h(C)+30kappa*B*K_h(C),
    Theta_sharp=Theta+30kappa*B*Omega.

The completed exact ordinary-moment identity splits into

    integral w(b-a)=Omega*I+sum w_i+ K_h(C_i)
                               +sum w_i+ L_i,
    L_i=(gamma-delta)*b_i-/9-(alpha-delta)*a_i-/15
                       -(2/45)*(delta_z-delta)*z_i-.

Here z is the actual zero-endpoint full12-to9 coordinate, and the
DIFFERENT source multipliers remain explicit.

The fine energy(1) improves the old z-b comparison to

    sup |z-b|<=C Hh^3,
    sum r_i*(|a_i-|+|b_i-|+|z_i-|)<=C Hh^5.

Indeed the completed variation-of-constants bound is
C[sqrt(H E_b)+Hh^3+sqrt(E_b S_cost)+h^2 sum r_i+S_cost];
use(1) and sum r_i<=sqrt(H S_cost). The own-preceding trace handles
the b part. Consequently

    |30kappa B sum w_i+ L_i|<=C Hh^7.              (4)

Substitute the EXACT ordinary identity into the EXACT storage balance,
then use(2)--(4). This proves

    6kappa integral w b^2
       =Theta_sharp*I+sum w_i+ Gamma_h(C_i)+R_h,
    |R_h|<=C Hh^(19/3).                           (5)

Every order-h^6 constant/source term is retained EXACTLY. Only the proved
smaller off-diagonal-state errors enter R_h. In particular Theta_sharp,
Gamma_h, I and the weights have not been replaced by reference-power
values or a physical ordinary clock.

Gamma_h is generally signed. Equation(5) is not an acquired endpoint
decoder, additive source action, nonnegative cocycle or action upper bound.
It leaves the full original source/phase implication unresolved.

## 4. Relative Taylor errors controlled by the OLD source action

Reuse the completed calibrated Phi_h>=0 and its literal unweighted action

    Action_h=sum Phi_h(C_i), ell_i=log(b2(B_i)/q_i),
    sum ell_i=H/4.

Action_h is the earlier A_h(K), distinct from the reference matrix entry A.
These are from REFERENCE-CALIBRATED-SOURCE-ACTION.md13747B/SHA
01f749193d5e5f4f59be4a83f32b7078f0e12141dc9895da3cf2a112ab7397de.
They are internal source quantities, not new source-menu equations.

There are fixed constants giving the pointwise bound

    u*s<=C H*Phi_h(C)+C*h^5*ell, u<=H.             (6)

Proof using the already completed branches: if F<=0 then Phi>=c*s.
If F>0 and u>=K h for the fixed large K of the old proof, Phi>=c*s too.
In either case u*s<=C H Phi. Otherwise F>0,u<K h; the old variance
bound gives beta<=C u, hence s<=C*v*u^5<=C*h^4*ell.
Then u*s<=C*h^5*ell. This covers ALL strict coins including rare ones.

Since r^2<=u*s/2, sum(6), retaining 0<w_i+<=1, proves

    h^2 sum w_i+*(u_i*s_i+r_i^2)
       <=C H*h^2*Action_h+C Hh^7.                      (7)

For any chosen epsilon>0, one sufficiently small FIXED budget makes the
first coefficient at most epsilon. Thus any bounded SAME-source Taylor
error of order u*s+r^2 has an action-absorbable remainder at this scale.
This is NOT an upper bound on Action_h. One must retain the factor h^2 when
using(7); an energy error h^(6+delta) is not automatically an action
error of the same order.

## 5. Reused all-n band algebra supplies a matched rate30 Psi receiver

This is a derived use of the OLD accepted general-n projective/Yule
identities and the completed all-n holding table, not another source
engine or cap ladder.

For n>=6 define on the n-to-(n-3) full band

    Psi_n(F)=(n-3)*w_n(F)/(n-5)-u_n(F).

The u_n,w_n are the old per-labelled comb and triple/cherry coordinates;
they are not the integrating factor w. For a BARE cell only, the old
bilinear reduction's general z_n formula, deletion identity and
6u_n+(n-4)w_n=-A_n/[3(n-3)] give exactly

    Psi_n(B)=[6P32_n-6P222_n-P4_n]/18.             (8)

For completeness, substitute A_(n-1)=A_n-
[2(n-7)P32+2P4-3(n-5)P222] into that old z_n formula. It yields

    (n-1)(n-2)z_n
       =2A_n/(n-3)+12P222-12P32+2P4.

Then Psi_n=-(n-1)(n-2)z_n/36-
[6u_n+(n-4)w_n]/6, proving(8). No bare identity is imposed on a word.
Left pair normalization scales both sides by exp(lambda_n*tau).

Its cubic source coefficient is v*beta^2/6 for EVERY n, by the same
three-merger routing count used at n7. The fair quartic coefficient is0:
the weighted history count and internal holding vectors cancel. The fair
fifth coefficient is1/192 for EVERY n. In the completed all-n holding
table let K1,K2,K3,K222,K4 be its five displayed polynomials. The weighted
H2(Lambda) and B2(Lambda,I) parts cancel, while EXACTLY

    18*(K1+K2+K3)-36*K222-18*K4=360.

The fair routing1/8, covariance factor1/4, simplex1/120 and contrast1/18
give360/(8*4*120*18)=1/192. This reuses the displayed OLD count table,
not a fit to selected n or a new coefficient execution.

For EACH fixed n the entire normalized fair-slice derivative and endpoint
factor v now give

    |Psi_n(C)|<=C_n*s,
    |Psi_n(C)-Psi7(C)|<=C_n*u*s.                   (9)

The cubic coefficients cancel for all coins. The difference is O(u^6)
at fairness, and its fair beta derivative is O(u^5); therefore the divided
quartic has beta^2 and the quintic has beta, giving precisely O(u*s).
No cap-uniform constant is asserted. Only fixed n12 is used next.

Let p30=Psi12(S)/(s9-s12)=O(h^4), and form the actual relative prefix

    p=Psi12(prefix)/k12+p30*(1-k9/k12).

It starts/ends at0 by COMPLETE commutation. Its ordinary equation is
p'=30(p-p30), source multiplier delta_z=d9/d12. The storage weight
still has delta=d4/d9. Zero-endpoint integration gives

    sum w_i+ Psi12(C_i)/d12_i
      =30p30 I-sum w_i+[
                    p30*(1-delta_z)+(delta_z-delta)*p_i-].

Variation of constants and(1),(9) give sup|p|<=C Hh^4.
The correction on the right, after multiplying by h^2, is O(Hh^8).
Removing d12 and replacing Psi12 by Psi7 use(9), r*s<=C H*u*s,
and(7). Thus, for every epsilon and one fixed small budget,

    |h^2 sum w_i+ Psi7(C_i)-30h^2*p30*I|
       <=epsilon*h^2*Action_h+C_epsilon*Hh^7.           (10)

The TWO real source transports were never set equal. This is the
action-controlled matching receiver, not a universal unweighted decoder.

The general-n identities in this section follow from the complete OLD
EXACT-BILINEAR-REDUCTION-CANDIDATE.md10259B/c7231884... and its
COMPLETE HAND ACCEPT3973B/b55981c2..., read at Commons8b96f4fb, plus
COUPLED-TRANSVERSE-CANCELLATION.md16844B/a28a9c35... and its all-n
counting appendix. Their original contributions remain PROVED/REUSE.

## 6. Exact terminal comparison and original remaining gap

The OLD rounding theorem and Phi_h>=c h^2 V_h already imply:
if ONE actual fitting word can be supplied with Action_h<=C h^(6+delta),
for ANY fixed delta>0, then

    V_h<=C' h^(4+delta),
    dist(nu,Z)<=C'' nu^(-delta/2).

Choose an integer k with1/k<=delta/2 and an integer large enough for the
constant to obtain the original AG bound. This is routine REUSE of the
old all-k arithmetic/rounding, not a new index theorem. No such action
upper bound is acquired here; h^7 was only one stronger sufficient test.

The actual new claims are(2)--(5),(7),(9)--(10). They reduce state errors
and matching remainders while preserving exact constants/weights. They do
not sign Gamma_h, fix I or provide Action_h/V_h from the endpoint. The next
original-goal action is a valid JOINT comparison of the sharp balance,
full-source constraints and relative action at the correct scale, or a
genuinely superseding source-complete route. Do not reopen energy, erase
diagonal weights, turn these necessary identities into a substitute goal,
or claim a phase from their powers alone.

R-only phase flexibility, source action LOWER bound, finite-diagonal
nonrecovery and the withdrawn categorical full-endpoint no-go remain at
their exact scopes. No new parameter tie, hidden observation, source
count bound, formal admission or original G3/G4 endpoint is added.
All verification is displayed HAND algebra/source-uniform estimates.
No source/model/tuple/coefficient/solver/native/Lean/Cargo/Lake/CI/QE
job, local Git write, new chat/worker, peer wake or held replay occurred.
