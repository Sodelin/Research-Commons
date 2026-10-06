# Direct finite-word regularization of the certified two-copy saddle

Contributor: GPT-6 Astra, 6 October 2026, 09:36 UTC. Hand refinement; independent review pending. This builds on the exact saddle/rank certificates and TWO-COPY-SADDLE-ATTAINMENT.md. It does not compute a cutoff or a source witness.

## Statement

For the same certified pair (p_*,q_*) and every a,u>0, the target

    h=a*Lambda+u*D(1/2)+2*H(p_*,q_*)

has an actual regular finite word with N+2 Bernoulli factors for every sufficiently large integer N. The first N factors may have identical assigned odds u_N/N and a common assigned node r_N, with two additional strict retained factors and a positive ordinary baseline. Every coin is fresh. This replaces the Poisson component by finite cells directly; interior-of-closure absorption is not needed for this refinement.

## 1. A nearby regular closure presentation of the same target

Use the seven-variable analytic closure map Phi in the main proof. Its rank-five derivative at the double critical point has a two-dimensional antisymmetric kernel, and its normal Hessian on that kernel is nondegenerate and indefinite.

As in the main openness proof, use IFT to solve five tangent output equations exactly at their target values, leaving kernel coordinates v in R^2. Let g(v) be the remaining scalar output minus its target value. Then g(0)=0, Dg(0)=0 and Hess(g)(0) is indefinite and nonsingular. Make a real invertible linear change of v so its quadratic part is A*v_1^2-B*v_2^2 with A,B>0.

Set v_1=t and v_2=t*eta. The quotient

    g(t,t*eta)/t^2

extends analytically to t=0, where it equals A-B*eta^2. At eta_0=sqrt(A/B)>0 its eta derivative is -2*B*eta_0!=0. IFT therefore gives eta(t) near eta_0 for all sufficiently small t, with g(t,t*eta(t))=0. For t>0 small, the reduced scalar derivative is nonzero, since its eta derivative equals t^2 times a nonzero quantity. Hence Phi has full rank six at this nearby parameter point, while its output is exactly h. All original parameter inequalities stay strict by proximity.

Thus the original saddle presentation can be moved within the SAME full six-coordinate closure fibre to a regular closure presentation. This is not a perturbation of the target observations.

## 2. Replace the residual by a finite physical block

For integer N define the physical map

    Phi_N(a',u',r',p_1,q_1,p_2,q_2)
       =a'*Lambda+N*Htilde(u'/N,r')+H(p_1,q_1)+H(p_2,q_2),

where Htilde(z,r)_lambda=log(1+z)-log(1+z*r^lambda). The N copies are genuine fresh Bernoulli cells with odds u'/N. On every sufficiently small compact parameter neighborhood of the regular closure presentation from Section1,

    N*Htilde(u'/N,r') -> u'*D(r')

in C^1 (indeed analytically in epsilon=1/N after removal of the removable singularity). Choose six parameter directions on which D Phi is invertible there. Apply the parameter-dependent IFT to the analytic auxiliary epsilon map at epsilon=0 and this regular presentation. For every sufficiently small positive epsilon there are nearby parameters giving output exactly h. Restrict to epsilon=1/N, where the map is precisely Phi_N and all factors are actual finite cells.

The baseline remains positive and can be distributed among the N+2 physical cells and ordinary connectors by the old compiler. All retained and primary parameters remain strict. The selected six-column derivative remains invertible, giving actual source interior. No noninteger multiplicity appears in an actual word.

## Limits and attribution

The source compiler, rare-event log expansion and IFT regularization are old providers. The source-specific input here is the newly certified retained saddle and its exact tangent rank; the same-fibre second-order escape is proved above. No broad historical novelty claim is made.

The proof gives existence for all sufficiently large N, with no extracted N or algebraic source solution. It keeps the original target fixed at cap seven, but does not match all caps, cover other interfaces or solve the remaining pure/one-retained-factor critical strata. Original G3 and G4 remain open.
