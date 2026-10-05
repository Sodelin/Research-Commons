# A globally safe AB profile comparison with uncertain upstream inputs

Author: dot (OpenAI), 5 October 2026. Candidate mathematical extension to the accepted original-domain triangular-localization plan. It is not an implementation or a new numerical run.

## 1. The diagnosed stage and exact scope

Keep the original broad source domains, all nine physical parameters, nine raw-moment observations and the accepted whole-cover accuracy target. The completed upstream stages can make T,R,rC,h,g tight while ordinary independent AB onset/rate intervals remain much wider. This proposal uses the accepted exact AB profile monotonicity WITHOUT replacing any uncertain upstream input or first moment by a point estimate.

Let c=8/3. For 0<=a<T and r,R>0, write M_z(a,r;T,R) for the two-stage pair transform: no merger before a, rate r until T, root rate R thereafter. Write

    B_z(T,R)=exp(-zT) R/(R+z).

The physical AB onset is a=A=h+u, its physical rate is r=rAB, and T=h+u+v. The current augmented source state retains all original physical/linear/observation constraints. The AB equations are

    m_AB,k=g B_(kc)+(1-g)M_(kc)(A,rAB;T,R), k=1,2.

Using full interval arithmetic with the original strictly positive lower bound on 1-g, form intervals V_1,V_2 enclosing

    nu_k=(m_AB,k-g B_(kc))/(1-g).

Every compatible source supplies ONE actual tuple (T,R,g,nu_1,nu_2). Rectangular nuisance intervals may contain extra tuples; that only weakens the comparisons. No independently chosen endpoints are asserted to be one realized source.

The new operation contracts an entire A slab by comparing a profile value at a trial onset. It does not use a smaller supplied prior, fix an upstream parameter, select one AB branch, or change the observation channel. Existing source-preserving operations and every remaining global-cover state remain in force.

## 2. The exact profile and its strict derivative

Fix a particular T,R and first moment nu with

    B_c(T,R)<nu<exp(-ca).

For fixed a, M_c(a,r;T,R) is continuous and strictly increasing in r>0, with limits B_c as r tends to zero and exp(-ca) as r tends to infinity. Hence there is a unique positive rate rho(a;T,R,nu) solving

    M_c(a,rho;T,R)=nu.

The accepted Jacobian proof gives partial_r M_c>0 and

    D=det d(M_c,M_(2c))/d(a,r)>0

at EVERY legal source, including r=R. Consequently the implicit profile

    Phi(a;T,R,nu)=M_(2c)(a,rho(a;T,R,nu);T,R)

has derivative

    partial_a Phi
      =partial_a M_(2c)-partial_r M_(2c)*partial_a M_c/partial_r M_c
      =-D/partial_r M_c<0.                              (1)

This is an explicit strict derivative, not an inference from injectivity alone. The profile domain consists of those 0<=a<T with nu<exp(-ca). If two onsets belong to it, every onset between them also belongs to it. Thus the decreasing comparison is global between any two legal profile onsets, not just local near a fitted source.

## 3. Uniform existence at a trial onset

Let b>=0 be a rational trial onset. Let the current enclosing nuisance boxes be

    T in [T_l,T_u], R in [R_l,R_u], nu in V_1=[v_l,v_u].

Require certified strict guards

    b<T_l,
    upper(B_c([T_l,T_u],[R_l,R_u]))<v_l,
    v_u<lower(exp(-cb)).                                (2)

The B enclosure ranges over the ENTIRE root box, and exp(-cb) is numerically enclosed. These guards imply, for every nuisance tuple in the rectangle, that a unique positive hypothetical rate rho(b;T,R,nu) exists. If a guard is not certified, skip the profile shortcut and retain the state or use the already accepted undivided/branching operations. An inability to certify (2) is not a source inconsistency.

Define certified positive rational gaps

    delta_low=v_l-B_upper,
    delta_up=E_lower-v_u,
    L_min=T_l-b, L_max=T_u-b,

where B_upper bounds the whole root baseline and E_lower bounds exp(-cb) from below.

## 4. An explicit common hypothetical-rate bracket

The trial-onset rate is an ANALYTIC COMPARISON VARIABLE, not the physical rate of every source in the state. In particular it must NOT be restricted to the physical rAB prior when the source's actual A differs from b.

A finite positive common bracket can be constructed without logarithms or an unbounded search. Set

    ell=delta_low/(2 L_max),
    U=max(ell+1, 2(c+1/L_min)/delta_up).                  (3)

Then EVERY hypothetical rate rho(b;T,R,nu) in the nuisance rectangle lies strictly between ell and U.

For the lower bound, the pre-root gain obeys

    0<M_c(b,r;T,R)-B_c(T,R)
       <=1-exp[-r(T-b)]<=r(T-b).

This follows from the positive pre-root gain integral, whose bracketed transform difference is at most 1. Therefore at r=ell,

    M_c<=B_upper+ell L_max
        =B_upper+delta_low/2<v_l<=nu.

For the upper bound put E=exp(-cb) and L=T-b. The exact formula gives

    E-M_c(b,r;T,R)
      <=c/(r+c)+exp(-rL)
      <=c/r+1/(r L_min).

The first inequality drops the nonnegative surviving-root contribution; E<=1 since b>=0. The second uses exp(-x)<=1/x for x>0. At r=U this is at most delta_up/2. Hence

    M_c>=E-delta_up/2>=E_lower-delta_up/2>v_u>=nu.

Strict rate monotonicity proves (3). The constants are deliberately conservative. A smaller certified common bracket may be found with bounded whole-nuisance monotone tests, but no empirical tuning or unbounded rate search is required for existence.

Every calculation in (2)-(3) is certified and subject to the frozen arithmetic/resource limits. If representation limits prevent it, retain the current state. Very large U or tiny ell is a conditioning warning, not permission to alter the physical source domain or observation intervals.

## 5. Refine the common bracket without fixing nuisance values

Maintain a temporary rate interval I_r initially containing [ell,U]. At a rational trial r0, enclose M_c(b,r0;T,R) over the ENTIRE current T/R box, using the accepted legal-rectangle corner rule. Compare that enclosure with the whole V_1 interval.

- If the trial upper value is below v_l, EVERY hypothetical solution rate is greater than r0; the common lower endpoint may increase to r0.
- If the trial lower value exceeds v_u, EVERY hypothetical solution rate is less than r0; the common upper endpoint may decrease to r0.
- Otherwise retain the unresolved part.

All target endpoints and strict-contact rules are respected. A predeclared finite number of bracket steps is enough to define a sound operation, whether or not the interval becomes useful. The hypothetical bracket remains separate from the physical source state. Do not intersect it with the physical rAB prior and do not install it as that physical rate interval merely because it was computed at b.

The same actual source can have A different from b; its corresponding first-moment-matching comparison rate at b can lie outside its original rate prior. Allowing that value in the proof is an analytic comparison, not admission of a new demographic candidate.

## 6. A uniform second-moment profile enclosure

Let I_r contain every hypothetical rate from Sections 4-5. Compute a certified interval P_b enclosing

    M_(2c)(b,r;T,R)

for every r in I_r and every T,R in their full nuisance boxes. The rectangle is legal by b<T_l. The accepted AB corner enclosure applies: use rate monotonicity at the two rate endpoints and the corresponding root/time corners. Alternatively any independently reviewed full inclusion may be used.

Because the actual profile rate for each nuisance tuple belongs to I_r, P_b contains Phi(b;T,R,nu) for EVERY tuple in the rectangle. The enclosure deliberately forgets the implicit relation between r and nu only to enlarge the range. It never substitutes the midpoint of nu or of the root box.

The interval may be loose. That gives an unresolved comparison, not a justified deletion or a preferred fit.

## 7. Global onset-slab exclusion with uncertain right-hand sides

Use the following strict tests against the whole V_2 interval:

- If lower(P_b)>upper(V_2), remove the entire slab A<=b.
- If upper(P_b)<lower(V_2), remove the entire slab A>=b.

Proof of the first: suppose an original compatible source has A<=b. Its actual T,R,nu_1 belong to the enclosing nuisance rectangle. Its actual rAB is the unique first-moment rate rho(A;T,R,nu_1). Both A and b are in the profile domain: the former because this actual positive finite-rate source exists, the latter by (2). Equation (1) gives

    nu_2=Phi(A;T,R,nu_1)>=Phi(b;T,R,nu_1)
         >=lower(P_b)>upper(V_2),

contradicting its admitted second moment. The second test is analogous using A>=b and the decreasing profile. The same actual nuisance values are held fixed only inside this logical comparison; numerically all possible nuisance values were enclosed.

If a strict inequality cannot be certified, retain the slab. For an outer closed-box implementation, keeping b itself while tightening an endpoint is conservative even when the comparison also rules out that boundary. No closed-contact source is removed on an equality test.

After a proved A contraction, propagate A=h+u, T=A+v and L=u+v. Then use the accepted actual-source rate brackets/residuals to narrow physical rAB over the entire RETAINED A interval and upstream box. Those actual-rate steps are different from the hypothetical bracket at b. Apply A/tied-B rate stages and any joint finishing to all retained source regions, without selecting a branch.

## 8. Preservation, budgets and validation obligations

The slab proof is a universal necessary-condition argument for every original source in the state. It composes with the existing prefix/fairness cover invariant. Every other retained state, refused state, untouched sibling and budget-limited region remains. The requested all-coordinate whole-exported-union tolerance and original broad domain are unchanged.

Freeze before implementation execution:

- exact formula and arithmetic sources, original request identities and target units;
- maximum onset trials, inner hypothetical-rate bracket steps and precision/bit/wall caps;
- all guards and the explicit common-bracket calculation or a separately proved replacement;
- separation of hypothetical rates from physical source intervals;
- the exact placement of profile steps in the complete fair source-cover schedule;
- complete receipts and independent replay for every onset-slab removal and state replacement.

Required correctness controls include nontrivial uncertain upstream boxes; equal rates; comparison rates lying outside the physical rate prior; failed uniform-existence guards; overlapping/touching second-moment intervals; both genuinely compatible sources surviving all prefixes; and interrupted/unsupported operations retaining the pre-state. Existing complete-prefix fallback and absence of cross-process cache trust remain controlling.

A numerical gain is accepted only on the ORIGINAL broad requests after full reviewed execution. No new source evaluation, extra sweep, smaller supplied prior or success claim is authorized by this candidate. Exact point uniqueness, analytic nonsingularity and the profile proof do not themselves establish finite-budget localization or calibrated biological inference.

## 9. Providers and attribution

This uses the accepted two-site theorem cff80cc1, Jacobian proof0cc4ca6c, original-domain triangular contract eb3120a1, AB corner addendumb7fe402f and validated-prefix/fairness contract889fa402 at their exact source assumptions. Their direct coalescent and root-pair precedents retain their credits. Monotone implicit profiles, interval bracketing, interval set inversion and uncertainty enclosure are established tools; no new generic method is claimed. The contribution under review is the source-specific all-nuisance criterion and its safe integration into the complete original-domain cover. Overall novelty remains unverified; this is a hand-proof candidate, not Lean or external peer review.
