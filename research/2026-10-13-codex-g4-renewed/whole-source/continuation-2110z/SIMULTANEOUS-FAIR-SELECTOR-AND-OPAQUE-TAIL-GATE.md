# Simultaneous fair selection and the remaining opaque-tail observer

Contributor: Codex whole-source lane, 14 October 2026. The simultaneous
lowest-blob proposal is due to the Codex lead G4 lane. **Hand-derived
linear identity and supplier-applicability checkpoint.** No full
INDEPENDENT-to-COMMON theorem, finite INDEPENDENT certificate, computation
or formal verification is claimed.

## 1. Exact selector identity

Suppose a specified finite source region has r opened hybrid sites. At
site i its two incoming ports are labelled (i,0),(i,1), and its natural
coin probabilities are p_i(0)=g_i and p_i(1)=1-g_i. Let H be its ENTIRE
completed response table on arbitrary finite allocations to all opened
ports and any retained outside inputs. The same actual upper continuation
is used in every row. The ports accept opaque forest roots; prebuilt
component trees are grafted into their selected roots, not independently
rerouted leaf by leaf.

For a vector k=(k_1,...,k_r) of incoming root counts and a fixed finite
outside allocation e, define the simultaneous COMMON selector by

 (C H)_(k,e)
   = sum_(sigma in {0,1}^r) [product_i p_i(sigma_i)]
       H_(((k_i 1_{sigma_i=0},k_i 1_{sigma_i=1}))_i,e).       (1)

This is an equality of probability measures on completed labelled trees,
so it also holds coordinatewise. It routes all current roots at each
specified site to one arm, with independent natural site coins. Formula
(1) preserves one source and its shared physical parameters. It does not
give permission to query the opened ports.

Let F be the set of fair sites, g_i=1/2, and let
G=(Z/2Z)^F act on response tables by swapping the two input-port names at
each chosen fair site. Write

       H_sym = |G|^(-1) sum_(s in G) s H.

**Fair-selector lemma.** For each s in G,

                   C(s H)=C(H),
               and therefore C(H_sym)=C(H).                  (2)

Indeed replace sigma by the vector obtained by flipping its coordinates
at the sites flipped by s. This permutes the summands of (1). The product
weight is unchanged because those sites are fair. The proof requires no
identifiability of H and no linear independence of its orbit. C is a
fixed linear operation on the full table; its definition uses only the
already specified natural coins and site/port grouping. Biased sites
are not included in G; their cohort masses can orient the ports, subject
to the inherited cohort-extraction hypotheses.

Thus an OBSERVABLY RECOVERED joint symmetrized port law would suffice to
commonize the entire specified region at once. Independent fair arm
orientation is not by itself an obstruction to this simultaneous step.
In particular, a reconstruction proof need not orient each fair site by
conditioning on an outside genealogy, an operation which could introduce
selection bias.

## 2. What the identity does not reconstruct

For a lowest reticulate blob, opening its sinks produces an ordinary
multiport region followed by a common upper continuation U. The proposed
bottom-up proof still has the following source and observer duties:

1. Determine from original completed INDEPENDENT observations which
   recovered descendant cuts belong to the same blob and which are its
   ordinary exits. The first-cut result identifies the youngest hybrid
   child cuts; it does not yet identify the whole blob grouping.
2. Determine and cancel the actual lower-subtree forest operators needed
   to place arbitrary opaque roots at those cut ports. At the first
   youngest cut its entire lower tree is ordinary and the accepted
   shared-cut proof supplies this operation. After earlier blobs have
   been commonized, a lower subtree can be a COMMON mixture; its full
   root-port operator has not thereby become an observed quantity.
3. Obtain the jointly symmetrized table H_sym with all required port
   allocations and their shared outside dependence. Separate marginal
   cohort laws do not determine this joint table. At disjoint known
   youngest sites the actual-cohort mechanism suggests a joint
   extraction, but a full changing-source blob induction must prove its
   input alignment and lower cancellations.
4. Recover enough of the opened ordinary multiport operator, modulo the
   fair swaps, to cancel it against the unknown common upper continuation
   U and proceed to higher blobs; or supply a direct equivariant law
   transform that avoids that cancellation. Equation (2) changes the
   routing of the specified region only. It does not change the older
   sites inside U, nor prove that this further change is linear on a
   mixture of unresolved upper sources.

These are not requests for independently accessible latent ports or a
known rival graph. They are the precise observations-to-source bridges
that would have to be proved from the original entire completed law.
The new selector identity discharges the orientation issue CONDITIONAL
on the required joint table and grouping; it discharges none of the
four observer duties by itself.

## 3. Targeted inspection of the full COMMON supplier

The inherited
[whole-COMMON directed-profile theorem](../../../2026-10-08-codex-g3-g4-full-shot-1253z/g4-effective-stopping/attempt-3/WHOLE-COMMON-DIRECTED-PATH-EXPOSURE-AND-STOPPING.md)
conditions on every source COMMON bit and obtains an ordinary population
tree with ordinary infinite Kingman completion Q. Its existing proof
does not supply the arbitrary shared-U observer required in Section 2:

* Sections 2--3 remove the common stem using E_s Q=Q and obtain the
  labelled comb probability kappa_(n+1) exp(-binom(n,2)L). The kappa factor
  is the ordinary ancestral completion probability. With an unspecified
  U, even the no-younger-merger sector instead retains a U-dependent
  completed-tree coordinate.
* Sections 6--7 prove independence and recover weights of whole ordinary
  profiles using the ordinary completion factors kappa_(m-s), with a
  polynomial bound on kappa_(m-s)/kappa_m. Those are not available merely
  from exchangeability and projectivity of an unspecified U.

This is an applicability limit of that proof, not a counterexample to an
unknown-upper analogue. Exchangeability does force uniform completed
triples and certain total-probability identities at four roots; it does
not fix every higher-root completed topology probability to its Kingman
value. A source-derived U is more restrictive than an arbitrary
exchangeable projective family, and any successful extension should use
that actual restriction rather than silently replace U by Q.

The calibrated original-taxon forest decoder is a different inherited
supplier. Its relevant input is disjoint calibrated exclusive words
with one fixed meeting interface. No claim is made that an arbitrary
opened multiport mixture meets that hypothesis. In particular, failure
of a particular balanced-topology probability to be positive is not a
valid refutation of that calibrated decoder: its balanced-colour comb
normalizations must be checked in their actual stated form.

## 4. Relation to the master question and checkpoint

The reviewed
[first-cut and biased-resolution note](ALL-LAW-INDEPENDENT-COMMON-SHARED-CUT-GATE.md)
already gives full-law INDEPENDENT-to-COMMON transfer in the all-biased
case and explains the fair mixed-port gap in its sequential recursion.
Equation (2) narrows that gap: simultaneous fair orientation can be
quotiented out, so it is not an impossibility argument. The remaining
task is a source-valid multiport observer/cancellation theorem, or an
exact admitted counterexample to the full-law implication.

Even a positive full-law implication would leave the fixed-target finite
INDEPENDENT prefix bridge unresolved. The
[reviewed discontinuity construction](INDEPENDENT-COMMON-TRANSFER-DISCONTINUITY.md)
prevents assuming a general continuity argument, and does not supply an
exact-prefix impossibility result. Natural BOTH forcing and its accepted
proofs remain separate.

Next action: test the common-upper-continuation multiport observer at its
precise source-derived interface. Do not treat the fair-selector identity,
profile reconstruction with Q, or a finite numerical rank screen as that
observer.
