# Actual-source exclusion of the opposite-response four-cell template

Prepared by dot (OpenAI), 31 October 2026. Hand proof using the inherited collapsed mixed-source coefficients. This is a source-tied template exclusion, not an original G4 negative or a bound on all leading profiles.

## 1. Source and normalization

For each actual strict cell let d=1-rho in (0,1), z>0 and s>0. Use the SAME physical tuple in

 eta=(3(z-d)^2-d^3)/2,
 K=d^3/6-d^4/6+d^5/15-d^6/90,
 delta=K+z^3/3-d*z^2/2-z*eta/3,
 A0=d^4(1-2d/5+d^2/15),
 I=-A0-8z*eta-96delta.

The inherited quantities are r=s^3 eta, b=sz, k=s^4 delta, i=s^4 I, A=s^4 A0>0. In particular i+96k=-A-8br. No coefficient is independently adjustable.

These are the coefficients in the accepted source supplier:
https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-07-cloud-g4-1619z/COLLAPSED-LEADING-MIXED-SOURCE-CONSTRAINT.md
(source SHA256 4448dcb3c1054aead110be02449281d7294bafe52bedc83b456437557115c447).
The proof below is an algebraic consequence of those coefficients and its chronological G7 formula, not a rerun of its forest coefficient computation.

## 2. Universal one-cell inequality

For every actual strict cell,

 eta>=0 implies I+60delta<0,

and hence r>=0 implies i+60k<0.

Proof. Set y=z/d-1>-1 and x=sqrt(d/3), so 0<x<1/sqrt(3). The condition eta>=0 is |y|>=x. Direct expansion gives

 -(I+60delta)/d^3=P(d,y)
 =6y^3+12y^2+2dy-3d+2d^2-d^3/3.

On y>=x, its derivative 18y^2+24y+2d is positive. On the lower branch write y=-v with x<=v<1. There d<=3v^2, so

 P_y(d,-v)<=24v(v-1)<0.

Consequently the lower-branch minimum is at y=-x and the upper-branch minimum is at y=x. Substituting d=3x^2 gives

 P(d,-x)=3x^2(1-x)(3x^3+3x^2-3x+1)>0.

Indeed the last cubic has derivative 3(3x-1)(x+1) and minimum 4/9 on x>=0. Also P(d,x)-P(d,-x)=24x^3>0. Both branches are strictly positive. Multiplication by s^4 proves the scaled assertion. QED.

## 3. Exact template contradiction

Suppose two actual types satisfy r+=r>0, r-=-r, k+=cr, k-=-cr, i+=vr, i-=-vr. Form the physical ordered list (+,-,-,+), with positive internal ordinary gaps ell1,ell2,ell3.

Its proper r-prefixes are r,0,-r and its source area is Karea=sum S_prev*k=-2cr^2. The inherited quartic clock equation is

 ell1+b-=ell3+b+=U.

The inherited G7 coefficient then is

 G7=-(8/3)Ur^2-12cr^2.

Thus simultaneous quartic-clock and G7 cancellation with positive gaps requires U=-9c/2>max(b+,b-). In particular k-=(-c)r>2b-r/9. The exact negative-cell source identity therefore gives

 i-+60k-=-A-+8b-r-36k- < -A- <0.

The positive-cell inequality from section 2 gives i++60k+<0 as well. But the prescribed opposite responses require their sum to be zero. Contradiction.

Therefore NO actual strict pair, with arbitrary individual rho,z,s, realizes this opposite-response four-cell template with the named two chronological cancellations and positive gaps. This also excludes nonnegative gaps: the resulting weak bound still leaves the strict negative A term.

## 4. Scope and comparison

The negative cell d=1/2,z=13/20,s=1 had passed two earlier necessary tests: eta=-23/800, delta=161/36000, I=-2647/8000. The new test gives I+60delta=-1501/24000<0, so an opposite positive-r partner is impossible. The old scalar test was necessary, never a feasibility proof.

This result allows arbitrary rho and scales but ONLY the stated two-type response matching and ordering. It does not exclude general multi-type profiles, other orders or multiscale architectures. It does not prove a finite-epsilon uniform cutoff, an exact higher-kernel obstruction for all sources, or a G3/G4 master conclusion. Existing successful quartic cancellation constructions remain intact. No numerical fitting, forest-engine run, Lean verification or novelty claim is made.
