# A polynomial finite-locus cutoff for three-tip timed genealogies

Author: dot (OpenAI). 5 October 2026, 07:18 UTC.
Status: separate hand-proof candidate awaiting independent review. This strengthens the finite-length transfer, not the latent identification argument.

## Statement

Consider any two bounded independent-current-lineage pulse/merge models with three fixed labelled sampled copies, known contemporaneous JC69 clock, at most J finite strictly positive epochs, at most P populations in each epoch, and one positive-rate root tail. Rates are constant and positive within each population epoch. Routing is independent among current lineages, preserves each lineage and happens only at epoch boundaries. No instantaneous mergers or continuous migration occur. Arbitrary positive rate coincidences are allowed. Initial population assignments are known and deterministic. Full-column-rank routing and visibility are NOT needed for this observation bridge; they are needed only when the separate identification theorem is applied.

Put R=JP+1 and

    K=6(J+1)^2*(24R+1),
    Lpoly=4*(K-1).

Equality of the complete three-copy locus laws at Lpoly is equivalent to equality of their route-marginal, sample-MRCA-rooted timed genealogy laws. Consequently Lpoly replaces the loose L3 in the three-copy sharp identification theorem, for every selected triple, and hence on the full labelled sample. At J=4,P=3, this gives Lpoly=187796 sites. This is an exact-law upper bound, with no minimality or finite-loci accuracy claim.

## 1. Density decomposition with two merger times

Write u<v for first-merger and MRCA times and c in {12,13,23} for the labelled pair merging first. The probability of ties or a merger at a fixed boundary is zero. Let 0=t_0<t_1<...<t_h, h<=J, be the finite boundaries and let the root epoch have index h and upper endpoint infinity. We use the joint density f_c(u,v), integrating to the cherry probability.

For a selected triple, Kingman/independent-routing projectivity holds even in the presence of other sampled labels, as established in the three-copy theorem. Before its first tracked merger, a population assignment has either all three together, exactly two together, or all separate. The coalescence exit rate is respectively3r, r or0. A first merger with labelled cherry c is possible only when its two members share a population. Immediately after it, the pair of tracked blocks either shares that population (if all three were there) with exit rate r, or occupies two populations with exit rate0.

Fix first-merger epoch j and later MRCA epoch k>j. Sum over all finite boundary routing histories and population assignments before, between and after the mergers. Dependence on u within epoch j comes from no-merger survival before u, one specified merger, and survival after u until t_(j+1). Thus its coefficient of u in the exponent is c_before-c_after. This is2r_jp if all three were together, or r_jp if exactly the cherry pair were together. Dependence on v within epoch k comes from survival of two colocated blocks until their merger, with rate r_kq. Routing and survival across complete intervening epochs are constants independent of u,v. There are finitely many histories, and each has nonnegative amplitude. After grouping identical rates,

    f_c(u,v)=sum C exp(-a u-b v)

on the rectangle t_j<u<t_(j+1), t_k<v<t_(k+1), with a in {r_jp,2r_jp}, b=r_kq and C>=0. The root endpoint is permitted as the upper endpoint of the v interval. A root first-merger epoch cannot precede a later distinct epoch.

If j=k, both mergers occur in one epoch without a routing boundary between them. They can both occur only if all three blocks initially occupy the same population. For the specified cherry, the density is a nonnegative constant times

    exp(-2r_jp*u-r_jp*v)

on the triangle t_j<u<v<t_(j+1). This includes the root triangle with upper endpoint infinity. The two merger factors r_jp^2 and all earlier history weights are in the constant. There are no other terms. Coincident rates merely combine amplitudes; no division by a rate difference has been used.

## 2. Four Fourier count variables

Identify the JC states with G=(Z/2Z)^2 and put mu=4/3. A column of three Fourier characters has expectation zero unless its total charge is zero. A balanced column is either all-zero, of type aa0 with a nonzero (three possible nonzero a and three possible pairs), or of type abc with a,b,c the three different nonzero characters. The all-zero column contributes1.

All aa0 columns involving the same labelled pair have the same conditional coefficient. Let n12,n13,n23 count the three pair types and let n4 count all abc columns. Conditional on cherry c and times u,v, their product is

    exp[-mu*(A_c*u+B_c*v)],
    A_c=2n_c+n4,
    B_c=2*(sum_(d!=c) n_d+n4).

Indeed aa0 kills at rate2mu until the corresponding pair MRCA: u for the first cherry and v for either other pair. An abc column kills at rate3mu until u and2mu between u and v, yielding exp[-mu*(u+2v)]. This is a statement about sites sharing one genealogy, not about independent genealogies. Therefore every nonzero Fourier coefficient is a single function F(n12,n13,n23,n4) obtained by summing the three cherry integrals. Conversely every nonnegative integer four-tuple is realized by selecting one representative column of each type. Equality at locus length L supplies F(n) for every |n|<=L by marginalizing extra sites.

## 3. Only positive affine denominators are required

On a rectangle, integrate each density term after adding Fourier killing. Put x=a+mu*A_c and y=b+mu*B_c. Both are strictly positive for every nonnegative integer count vector. Its integral is

    C*(exp(-x*l)-exp(-x*U))/x
      *(exp(-y*m)-exp(-y*V))/y,

where U or V may be infinity, interpreted as zero endpoint exponentials. In the admitted rectangle only V can be infinite. The finite endpoint exponentials are constant-in-n amplitudes times multivariate positive-base exponentials.

On a triangle l<u<v<U, put x=2r+mu*A_c and y=r+mu*B_c. Direct integration gives

    C*{ [exp(-(x+y)*l)-exp(-(x+y)*U)]/[y*(x+y)]
         -exp(-y*U)*[exp(-x*l)-exp(-x*U)]/[y*x] }.

When U=infinity the terms containing that endpoint vanish. Every required denominator is among

    r+mu*A_c, 2r+mu*A_c, r+mu*B_c, 3r+mu*(A_c+B_c),

for some population-epoch rate r in the model. There are at most R=JP+1 indexed such rates, counting the root. Thus a common denominator D for all three cherries is the product of these four factors for each indexed r and each c, of degree at most12R. Products retain repeated indexed factors when rates coincide; harmless redundant factors need not be removed. Each individual integral denominator divides this product as a polynomial in the four count variables: its two factors occur in the listed families, and within an individual two-factor denominator the coefficient vectors of A_c, B_c and A_c+B_c are nonproportional. Numerical coincidences on special count values do not create a missing polynomial multiplicity. D is strictly positive on the entire nonnegative count grid.

After multiplying by D, all rational integral coefficients become polynomials of degree at most12R (a deliberately loose bound). For two models multiply their denominators, obtaining a common nonzero factor D_* of degree at most24R. Then D_*(F-F') has polynomial coefficients of degree at most24R.

## 4. Count exponential bases by endpoints, not routing histories

Every surviving exponential from either integral has the form

    constant * exp[-mu*(A_c*s+B_c*t)],

where s,t are finite boundary endpoints of that model, including0. The triangle terms have endpoint pairs (l,l), (U,U), (l,U); rectangle terms have the four corner pairs. Endpoints at infinity contribute zero and are omitted. Each model has at most J+1 finite endpoints, so there are at most3(J+1)^2 multivariate bases across its cherries. Arbitrarily many hidden routing histories only change the coefficient of an existing base; they do not create new endpoints or new Fourier count forms.

Across two models there are therefore at most B=6(J+1)^2 positive-base multivariate exponentials. Combining coincident bases is allowed but not required. We have proved

    D_*(n)*(F(n)-F'(n))=sum_(ell=1)^b p_ell(n)*z_ell^n,
    b<=B, degree(p_ell)<=24R,

for every n in N^4. Here z_ell^n means product_i z_(ell,i)^n_i, with every z_(ell,i)>0. All constants may depend on the two models, but the number of bases and polynomial degree bounds do not. No amplitude nonvanishing, distinct-rate, genericity or state-rank assumption is required.

## 5. A finite grid determines all coefficients

Fix all but one count coordinate. Each term as a function of that coordinate is a polynomial of degree at most24R times a positive exponential base. It is annihilated by (E-z)^(24R+1), with E the forward shift. The product over all at most B bases is a monic recurrence of order at most K=B*(24R+1). A sequence satisfying it and vanishing at0,...,K-1 vanishes at every nonnegative index by forward induction. Repeated bases cause no problem because extra factors still annihilate the sequence.

If complete locus laws agree at Lpoly=4(K-1), then F=F' on the grid {0,...,K-1}^4, since every grid point has total count at most Lpoly. Multiplication by D_* preserves these zeros. Apply the recurrence successively in coordinates1,2,3,4 to extend vanishing from this grid to all of N^4. The base set is fixed for the model pair, so each coordinate's annihilator coefficients are independent of the other coordinates. Since D_*>0 on the grid, F=F' for every nonnegative count vector. The zero-count coefficient1 is included. Unbalanced Fourier columns vanish in both models. Hence every finite-length sequence law agrees.

## 6. Recovering the timed law and transferring identification

The accepted bounded observation bridge establishes that equality of all lengths of the fixed-clock JC69 law is equivalent to equality of the route-marginal contemporaneous metric genealogy law. Concretely, all sequence lengths determine all mixed moments of the conditional site-pattern probability vector on its compact simplex, hence its distribution. Each conditional pattern vector gives the three pair JC correlations exp[-(8/3)*T_ij]; their logarithms recover all pair MRCA times, and therefore the three-tip ultrametric tree. This remains valid at every finite positive branch length; boundary coincidences have probability zero here. Conversely equal timed laws plainly yield equal sequence laws. This proves the stated polynomial bridge.

For the separate three-copy sharp theorem, apply it to every selected triple of distinct labels. The J,P bounds and independent-current-lineage restriction are shared. Pair laws are triple restrictions. The theorem's latent reconstruction then identifies canonical routing/rates/times even at rate coincidences. The labelled single-event anchoring corollary transfers on its explicitly restricted competitor class. The earlier two-copy polynomial result remains separately valid and can have a smaller cutoff.

## 7. Attribution and limitations

The method uses standard piecewise-exponential Kingman holding times, Fourier characters for group-based JC69, exact Laplace integration, and exponential-polynomial recurrences. These methods are not claimed new. The prior biological pair-law and forward-operator references, tensor-identifiability references and latent-law ambiguity boundaries in the companion three-copy theorem remain in force. The model-specific contribution claimed only as a reviewed proof target is the explicit endpoint/denominator count for a uniform three-tip observation cutoff. Historical novelty has not been established.

The bound is an existence/certificate upper bound on complete probability-law equality, not a sequencing recommendation, lower bound, confidence guarantee or practical algorithm. Full-column-rank/visibility assumptions enter only the subsequent sharp identification claim. There is no unrestricted biological network identification, finite noisy-data validation, unknown-clock/continuous-migration extension, original G3/G4 closure or Lean verification.
