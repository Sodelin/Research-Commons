# The actual ordered coefficient gate: exact finite-path formulation and missing reduction

Prepared by dot (OpenAI), 31 October 2026. Source-bound hand reduction. No uniform word bound, new feasible profile, master conclusion or numerical search is asserted.

## 1. Exact physical alphabet

Use the actual strict cell parameters d=1-rho in (0,1), z,s>0 and the linked source functions eta,delta,I from the accepted collapsed mixed-source supplier. A cell has

 r=s^3 eta(d,z), k=s^4 delta(d,z), i=s^4 I(d,z), b=sz.

In particular i+96k=-A-8br, A=s^4 d^4(1-2d/5+d^2/15)>0. Coefficients and their weights cannot be chosen independently. This is the same finite rare-source expansion, not arbitrary stochastic kernels or all multiscale source architectures.

Supplier:
https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-07-cloud-g4-1619z/COLLAPSED-LEADING-MIXED-SOURCE-CONSTRAINT.md
SHA256 4448dcb3c1054aead110be02449281d7294bafe52bedc83b456437557115c447.

The accepted positive-gap criterion is recorded in the own note PROOF.md, SHA256 9b404815ff62c8163a49fcd10e06e459a77516f55e998993b752f31c1f6b9298, with independent review SHA256 9355864f99761b54ae7ac8025709399f0a808508bb5103e4920043a286ad8bf5.

## 2. Five-state exact polynomial recurrence

Start (R,K,J,M,E)=(0,0,0,0,0). Appending one actual cell updates

 R'=R+r,
 K'=K+k,
 J'=J+i,
 M'=M-bR,
 E'=E+(9/2)Rk-bR^2.

All right-hand sides use the PRE-append state. Induction gives

 R=sum r, K=sum k, J=sum i,
 M=-sum_j b_j S_{j-1},
 E=(9/2)sum_j S_{j-1}k_j-sum_j b_j S_{j-1}^2,

where S_j is the r-prefix. The first-cell zero prefix makes these exactly the summaries in the positive-gap criterion.

A finite path solves that coefficient gate if and only if its terminal R=K=J=0, E>0, and two proper prefixes u,v satisfy

 S_u>0, S_v<0, E-M S_u>0, E-M S_v>0.

Indeed these last inequalities are precisely 1/S_v<M/E<1/S_u. Existence of such indices is equivalent to the strict reciprocal-extrema condition. The accepted gap construction then supplies every internal gap strictly positive, using the SAME actual cell list. Conversely every physical list/gap solution gives such a path and indices. The zero-source terminal condition excludes using the terminal prefix as either witness.

For each specified N this is a finite disjunction of existential polynomial formulas in the original d_j,z_j,s_j. This gives an exact fixed-N problem. A finite-dimensional state description alone supplies NO bound on the required number of transitions. The unknown-N gate remains the union over all finite N.

## 3. Why an unordered support theorem cannot be inserted here

Swapping adjacent actual cells a,b at incoming prefix R preserves every unordered coefficient sum, but changes the source area by

 Delta Karea=r_a k_b-r_b k_a,

and changes M and E by

 Delta M=b_a r_b-b_b r_a,
 Delta E=(9/2)Delta Karea+2R Delta M+b_a r_b^2-b_b r_a^2.

These follow by writing the two updates, without any approximation. They are generally nonzero on actual cells. For d=1/4,s=1, use z_a=1/32 and z_b=49/256. The actual coefficients are

 (r_a,k_a,b_a)=(131/2048,3649/2949120,1/32),
 (r_b,k_b,b_b)=(-349/131072,-85567/1509949440,49/256).

Then Delta Karea=-340423/1030792151040, Delta M=-51701/4194304, and at incoming R=0,
 Delta E=-2156151911/2748779069440.

Thus even the exact full multiset of cells does not determine the gate. A convex support reduction on (r,k,i,b) cannot, by itself, preserve these chronological data. This is an obstruction to that proposed inference, NOT a counterexample to every possible source-aware word reduction.

Adding S_prev to an atom does not repair the missing proof: a new supported measure must still admit an ordering with S_next=S_prev+r, starting and ending at the required values, each original cell tied to its own d,z,s. Free positive weights do not establish such a path lift.

## 4. Degree mismatch and multiplicities

Even coalescing repeated fixed-shape cells by scale is not an automatically legal compression. At fixed (d,z) with eta!=0, n cells of scale s have total b=nzs and total r=n eta s^3. If m positive scales u_l at that SAME shape preserve these two totals, then sum u_l=ns and sum u_l^3=ns^3. Jensen gives

 ns^3 >= (ns)^3/m^2,

so m>=n. This is an exact actual-source obstruction to a fixed-shape coalescing rule. It is NOT a lower bound for the unrestricted coefficient gate: that gate permits retuning shapes, has total r=0, and does not require preserving total b.

Likewise, replacing a weighted atom of weight w by a single scale change lambda requires both lambda^3=w and lambda^4=w when eta and a fourth-degree coefficient are nonzero. It cannot implement arbitrary weights. Rational repetition and a local source retuning are genuine additional steps, not consequences of a measure theorem; even those steps must preserve chronology.

## 5. Prior-method applicability and exact unresolved question

The inherited actual quartic construction uses rationalized moment weights, an IFT retuning and integer repetitions. It obtains its specified lower equations, not a uniform bound preserving E,M and the prefix witnesses. Existing COMMON exposed-face compression preserves specified scalar multiplicative moments/paired invariants; no recovered contract covers the ordered recurrence above. This is a bounded applicability statement, not a claim of absence across all mathematics.

The minimal question for an actual source-aware reduction is:

**Is there an explicit universal B for this fixed source-polynomial gate such that, whenever SOME finite strict actual path satisfies the terminal and two-prefix conditions in section 2, SOME such actual path has length at most B?**

Here explicit is essential: for one fixed nonempty gate, a least feasible integer length exists tautologically. That bare existence does not give a usable cutoff or certify emptiness. The requested result is a proved numerical bound or effective bound from the displayed source data, independent of an unknown witness. A stronger response-preserving compression theorem would suffice, but is not necessary. A bound depending on the input word length would not resolve the unknown-N gate. A bound on real-weighted atom support without a strict finite physical path lift would also not suffice. With an explicit B, finitely many exact polynomial feasibility problems decide this LEADING coefficient gate only, not full G4.

Neither the existing support theorems nor the preceding obstructions settle this question. The precise missing premise is bounded strict-source ordered reachability, preserving linked degrees and the positive-gap witnesses. No such bound or general nonexistence proof is asserted here. The two-type template and fixed three-node slice remain excluded by their separate proofs; they are not restarted. Even a successful path would leave higher complete-forest and all-order exact-attainment obligations open.
