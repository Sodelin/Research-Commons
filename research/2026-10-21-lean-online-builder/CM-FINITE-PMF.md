# One existing finite PMF to the existing CM law

CMFinitePMF.lean3949B/SHA256
f23c4428e1f5bad8f2d3675caa1684b66377acf4cfe34451b6be767d4e97d4c7
packages an existing finite PMF as the existing FinitePositiveLaw. It reuses
the literal positiveSupportPMF and gridWeight declarations, without a new
grouping algorithm, normalization or physical-source axiom.

For supplied p:PMF iota and x:iota->Real, only positive-mass rows require x>0.
The nodes are the distinct image of {i | p(i)!=0}; weights sum every retained
preimage mass. The checked endpoints prove:

- grouped_moment for EVERY natural exponent, including zero, against all
  original weighted rows, with zero rows omitted only internally.
- Strict positivity of grouped weights and exact mass one.
- fromFinitePMF_moment into the SAME CM law for every exponent and
  fromFinitePMF_sparse_moment at every k.choose2.
- Ioc(0,1] for nodes when positive rows separately satisfy x<=1.
- fromFinitePMF_weight_mapped_mass: the law's weight at every real a is
  exactly ((p.map x)(a)).toReal, including outside its node set.

The constructor is noncomputable semantic packaging of a supplied real PMF.
It does not compute hidden real source weights or turn estimates into exact
moments. The native rational-bank contract remains a separate effective input
with its own parser/grouping/provenance refinement obligations.

Seven selected endpoints passed actual Lean4.35.0/mathlib56a005 hosted checks,
only propext/Classical.choice/Quot.sound, no errors. The first proof attempt's
subtype-sum conversion failed and remains retained; the successful proof
uses the explicit Finset.sum_coe_sort equality. Benign inherited polynomial
deprecation/unused-simp warnings remain in the encrypted originals.

This bounded virtual document projects EXACT selected helper declarations
from pinned original source bodies, keeping their original names and proofs:
bind_probability_real, gridWeight and its moment/mapped-mass helpers,
positiveSupportPMF and its positivity/sum/map helpers, and finiteBankMoment.
CM-FINITE-PMF-SOURCE-MAP.json binds each complete parent source, literal
extraction boundaries and selected-body hash. The unchanged accepted CM
supplier/foundations and new wrapper are also included. This checks the
mathematical adapter, NOT the complete original physical imports or calendar
semantics. CHECKED-FOLLOWONS.json has all seven complete printed types.

The actual original randomized readout supplier remains
DotG4.WholeProfileDetermination.actual_randomized_legal_moment, with the ONE
configurationBankPMF of the shared configuration and original register. It
relates every positive copy level to finiteBankMoment of that law. Instantiating
the new semantic constructor retains its original graph/calendar/mask/readout
and support-domain obligations. Scalar pushforward equality alone does not
identify a joint source or physical realization.

A separately prepared540-module native source context makes the full imports
concrete; see native/physical-pmf/README.md. Its original physical sparse
supplier is imported ONCE through a separately hashed CMFoundations import
variant. The extracted duplicate is absent. Full import elaboration, native
Lake/object/full-owned-axiom acceptance and writer binding are still OPEN.
