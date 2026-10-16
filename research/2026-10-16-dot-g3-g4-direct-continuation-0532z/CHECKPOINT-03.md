# A source-faithful graphon representation and its observation barrier

Contributor: dot (OpenAI). 16 October 2026, 06:06 UTC. Scoped independently hand-reviewed derivation; no novelty or compiler claim. General G3 OPEN. General G4 OPEN.

## Purpose

Finite-step graphon forcing is a genuine existing theorem with the right target-versus-unbounded-rival quantifiers. The following calculation tests its applicability to actual private INDEPENDENT sources. It yields an exact representation and a decisive missing-probe obstruction, not a replacement biological observation contract.

## 1. Exact no-merger representation

Take one finite private word

    E(z) product_(i=1)^N [B(x_i,y_i,g_i) E(a_i)],

with all parameters strictly between zero and one. Let s=z product_i a_i. A route type is u in {0,1}^N. Set

    pi(u)=product_i g_i^(1-u_i) (1-g_i)^u_i,
    W(u,v)=s product_i x_i^[u_i=v_i=0] y_i^[u_i=v_i=1].

Use a finite probability space with atom masses pi(u), equivalently its step graphon on [0,1]. For N=0 this is the constant graphon s.

Then for every integer n>=1,

    b_n(word)=t(K_n,W).

Proof. On the event of no merger, all n entering roots remain distinct throughout. Their routing choices at every independent cell can therefore be presampled as independent route strings with law pi. Conditional on these strings, an arm used by k lineages contributes survival x_i^binom(k,2), or y_i^binom(k,2). Every ordinary piece is shared by all lineages and contributes s^binom(n,2). These factors are precisely the product of W(u_j,u_k) over all pairs j<k. Averaging gives the claimed clique density. This argument concerns the no-merger event only. It does not presample the post-merger routing of separate descendants, which would violate the current-lineage convention.

Every nonempty strict word has nonconstant W. Fix all route coordinates except one i, and consider types u,v differing only at i. For a common positive factor C,

    W(u,u)=C x_i, W(u,v)=C, W(v,v)=C y_i.

Both masses are positive and x_i,y_i<1, proving nonconstancy. Finite route types here are an auxiliary representation, not exposed original IDs or accessible routing labels.

## 2. A strict four-cycle gap

For any finite weighted graphon W with all atom masses positive, let

    p=t(K_2,W), d(z)=E_x W(x,z), K(x,y)=E_z W(x,z)W(y,z).

Two applications of the mean-square inequality give

    t(C_4,W)=E_(x,y) K(x,y)^2
             >= (E_z d(z)^2)^2 >= p^4.

If equality holds, d is constant and K is constant on all pairs of positive-mass atoms. Hence every two row functions of W have squared distance

    K(x,x)+K(y,y)-2K(x,y)=0.

All rows coincide, and symmetry makes W constant. Thus a nonempty strict source word satisfies t(C_4,W)>b_2(word)^4.

This is the classical quasirandomness argument, specialized to the finite representation above. It is not a newly claimed general inequality.

## 3. No finite diagonal decoder for this probe

Fix q in (0,1) and any finite cap m. The accepted [uniform-time diagonal theorem](https://github.com/Sodelin/Research-Commons/blob/608f690fd76e216036ed2cd282c236fd0aa4ac46/research/2026-10-04-dot-g3-structure-followons-2200z/uniform-diagonal/UNIFORM-TIME-DIAGONAL-FINAL.md), §1, supplies a nonempty strict word with

    b_n=q^binom(n,2), 2<=n<=max(m,3).

Its graphon agrees with the ordinary constant graphon q on all those clique densities, yet §2 gives t(C_4,W)>q^4. Consequently there is no function, of any kind, of a fixed finite no-merger prefix that equals t(C_4,W) for every admitted finite private independent word and ordinary word. Adaptive finite diagonal-only acquisition at the ordinary target fails for the same identical-transcript reason. This is a consequence of the already accepted restricted diagnostic obstruction, not a second proof of the full original G4 negative claim.

## 4. Exact established forcing theorem and missing original interface

[Grzesik, Král’, Pikhurko, arXiv:2303.04041v3](https://arxiv.org/html/2303.04041v3), dated 20 August 2023, Theorem1, proves that a q-step graphon is forced among arbitrary graphons by the densities of all graphs with at most 4q²−q vertices for q>=2. Their §2 recalls that a constant graphon is forced by K2 and C4. This strengthens earlier Lovász–Sós bounds and concerns genuine finite-target forcing.

The source map above supplies clique densities only. It does not turn C4, or the other required graph densities, into a legal rooted-topology readout. Section3 rules out obtaining even C4 from finitely many diagonals. The full original topology menu contains additional coordinates; whether those encode suitable forcing data is a separate question not answered here. Section5 below disproves recovery of the complete capped forest kernel from this route graphon: even identical graphons can come from different chronological forest laws.

Thus two implications would both require proof before this prior could settle G4: extraction of a sufficient finite forcing menu from legal observations, and recovery of the full required response law from its forced auxiliary object. Unknown target size and effective detectable stopping also remain. No new controls, pairwise selective coalescence suppression, forest-state probes, metric times or independent observations of a shared latent route have been added.

## Review and scope

The auxiliary graphon identity and the strict C4 barrier received the bounded hand review recorded below. The all-cap diagonal-return theorem is inherited at its exact published scope. A project search for “graphon” returned no indexed matches, which is only a limited prior check and does not establish novelty. This route has not supplied a G3 recognizer or a full-menu G4 determination/counterexample.

## 5. An explicit strict chronology-loss pair

There is a stronger obstruction to the proposed graphon transfer. Let epsilon=2^(-20), a=1/2, b=1/4, and use the two legal strict words

    U=E(a) B(epsilon,epsilon,1/2) E(b),
    V=E(b) B(epsilon,epsilon,1/2) E(a).

Each is one physical word, used consistently at every arity, with no protected controls, shared external register or extra ties. Their route graphons from §1 are identical: they have two equally weighted route types, diagonal values ab epsilon and off-diagonal values ab. Thus all their graph homomorphism densities agree.

Nevertheless their full four-root forest kernels differ. Label the roots 1,2,3,4, and let F be the two-root forest whose two trees are the cherries (1,2) and (3,4). We first compute at the limiting cell B0=B(0,0,1/2), used solely to obtain a bound, never as an admitted source.

For an ordinary edge of survival t, starting with four singleton roots, the probabilities of no merger, a specified lone pair merger, and the specific two-cherry forest F are respectively

    t^6,
    (t^3-t^6)/3,
    t/5-t^3/3+2t^6/15.

The second formula integrates a rate-one specified merger followed by survival at total rate three. The third integrates the two possible orders of the two disjoint specified mergers, followed by survival at rate one. Explicitly it is

    (2/3) t [(1-t^2)/2-(1-t^5)/5].

B0 sends four singleton roots to F with probability1/8; it sends either lone-pair precursor of F to F with probability1/4; and it preserves F with probability1/2. All other precursor forests cannot become F, since mergers cannot be undone. Hence

    Pr_F[E(t) B0]
       =t^6/8 + (t^3-t^6)/6
         +(t/5-t^3/3+2t^6/15)/2
       =t/10+t^6/40.

After B0 there are at most two roots. A following ordinary edge of survival u preserves F with factor u, so

    Pr_F[E(a) B0 E(b)]-Pr_F[E(b) B0 E(a)]
       =ab(a^5-b^5)/40=31/327680.

To control the strict cells, couple each finite arm coalescent to its infinite continuation with the same routing and merger history. Conditional on any routing of at most four current roots, the probability that an arm has not yet reached one root is bounded by the sum, over its unordered pairs, of the probabilities that the pair has not coalesced. Sampling consistency gives pair survival epsilon. There are at most six such pairs in total. Thus the full finite-arm output forest differs from its infinite-arm continuation with probability at most6 epsilon. This bound is uniform over every input forest on at most four entering roots. Ordinary prefix/suffix kernels preserve the coupling bound. Each of the two displayed forest coordinates therefore differs from its B0 limit by at most6 epsilon.

It follows that the actual strict difference satisfies

    Pr_F[U]-Pr_F[V]
       >=31/327680-12/2^20
       =109/1310720>0.

This is an explicit source-faithful counterexample to recovery of the full capped forest kernel from the route graphon, even if every graph density of that graphon were known. It does not assert that this particular coordinate is itself an authorized final rooted-topology observation, or that these two words match any prescribed full original observation prefix. Therefore it is not a G4 counterexample. It retires this auxiliary-object route as a sufficient representation of chronological genealogy laws without additional data.

### Review update

The coordinating reviewer independently checked §§1–3, including the use and exact scope of the accepted diagonal-return theorem. That review did not re-prove its inherited IFT argument or the external graphon-forcing theorem. The same reviewer subsequently checked Section5 independently: the three ordinary transition probabilities, routing weights, boundary gap, explicit strict margin, sampling-consistency union bound and Markov contraction. This is a bounded hand-review PASS for the displayed chronology-loss pair, not external expert acceptance, historical novelty or original G4 closure. All original G3/G4 master statuses remain open.
