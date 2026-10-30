# Exact paired clocks do not supply the missing prefix sign

Author: dot (OpenAI),30October2026. Author hand derivation, not independently
reviewed. This is a source-faithful countercontrol to ONE proposed inference;
NOT an exact commuting rival, AG-Pair counterexample or G3 theorem.

Use precisely the reference/source/normal conventions and accepted biased-saddle
calculation in fullcap-normal/WHOLE-WORD-FAIR-RIGIDITY.md,Section8, within the
public fair/joint source archive pinned by CHRONOLOGICAL-RATIO-ADAPTER.md.

Fix sufficiently weak h>0 and N>=2. Let H=4Nh, x=exp(-u*) with
u*=log(2exp(h)-1), so the original fair reference S(h) has COMMON exposure4h
and I-pair exposure3h. Choose beta>0 sufficiently small, and the actual strict
coin g=(1+sqrt(beta))/2. Set u=u*+2beta and let B=B(u,g) be the equal-arm cell.
The inherited source identities at u=u*,beta=0, with x held fixed, are

 f4=f4_u=f4_beta=0,
 f4_u,beta=-2f4_u,u,
 (f4_beta,beta-4f4_u,u)/(1-x)^4 -> -826875/22 as x->1 from below.

They are precisely equations(4),(10) and Section8 of the pinned whole-word
fair proof, with exact coefficient evidence in check_bias_saddle.py and its
source bank. They are reused, not independently rederived in this note.
For F(beta)=f4(exp[-(u*+2beta)],beta;x), chain differentiation in the u
coordinate therefore gives F(0)=F'(0)=0 and

 F''(0)=f4_beta,beta+4f4_u,beta+4f4_u,u
       =f4_beta,beta-4f4_u,u.

Since the displayed scaled limit is strictly negative, there exists a fixed
weak interval x0<x<1 on which F''(0)<0. Fix x there FIRST. Analyticity then
gives F(beta)=F''(0)beta^2/2+o(beta^2)<0 for sufficiently small beta>0.
No uniform-in-h size of this beta neighborhood is asserted. The original
coin g=(1+sqrt(beta))/2 is strictly interior for0<beta<1; smoothness in that
original coin parameter is not required for existence of these finite cells.

The exact cell diagonal and paired loss are

 b2=(1-beta)/2+(1+beta)exp(-u)/2,
 ell=u+log b2=log[((1-beta)exp(u)+(1+beta))/2].

At beta0,ell=h. Define h'=h-ell/N and r=4ell-u. At beta0,
h'=h(1-1/N)>0 and r=4h-u*>2h>0. By continuity both remain strictly
positive for sufficiently small beta. Consider the actual ordered word

 K=O(r/2) B S(h')^N O(r/2).

All cells and ordinary populations are strict. The reference powers retain their
positive bookends; adjacent ordinary factors may be combined without changing
the physical chronological kernel. Original parameters are shared between the
COMMON and INDEPENDENT interpretations; no separate retiming is performed.

The COMMON total exposure is
 r+u+4Nh'=4Nh=H.
The I-pair exposure is
 r-log b2+3Nh'=r+u-ell+3Nh-3ell=3Nh=3H/4.
Thus BOTH paired clocks agree exactly with S(h)^N at the SAME reference h.

For the FIRST actual bare cell B, its whole-word coefficient W4_1 is strictly
positive. Consequently s1=W4_1 f4(B)<0, and the chronological partial sum
S1 is negative. All cells can be placed in the adapter's weak interval by taking
H small enough and then beta small. Its normalized ratio remains decreasing.

This word is NOT asserted to commute with S(h). In fact its remaining complete
commutator equations are the information deliberately absent from this test.
Therefore the construction only rules out deriving S_k>=0 from strict source
admission, both exact clocks, and monotone normalized transport. It does not
rule out a prefix estimate conditional on full commutation, a signed joint
phi5 estimate, or a SAME-defect relative action argument.

The countercontrol reuses existing saddle and exact-clock compensation ideas;
it is an explicit new use-site check, not a novelty claim or new family of
fitting sources. No numerical residual, free local mixture or approximate
endpoint is promoted to an exact solution.

## Review scope —30October2026,18:57UTC

The coordinating root agent checked the b2 and ell formulas, both exact clock
identities, and positivity of h' and r at beta0 followed by continuity, given
the inherited S(h) exposures. The negative-normal conclusion remains conditional
on the cited inherited mixed-derivative/saddle identities; that source algebra
has not been independently rederived by this reviewer. No approval of an exact
commuting counterexample or original G3 conclusion is implied.
