# One rational bank, all sparse moments

The native input proposal remains owned by the existing Rust builder. Its
schema rational_finite_bank_moments_v1 supplies one atom array and L1..8.
Positive rational masses require survival in (0,1]; exactly zero masses can
carry arbitrary rational values and contribute zero to every moment. Total
mass must already be one. There is no normalization or approximate equality.

For positive carrier A={i|w_i>0}, take its exact survival image S and group
W(s)=sum of ALL positive preimage masses. Required mathematical equations are
W(s)>0 on S, sum_S W=1 and, for every natural n,

    sum_(s in S) W(s)*s^n = sum_raw_i w_i*x_i^n.

The same S,W must be fixed before querying k. Moment k uses n=k.choose2;
positive copy levels1,2,3,... give0,1,3,... . Original zero-mass out-of-domain
rows are not fed to a theorem requiring ALL listed values in (0,1]. The
checked normalized-bank cast theorem applies to the retained/grouped carrier.

New checked source lean/RationalBankMoments.lean proves cast_moment and
cast_normalized_bank: exact finite rational moments commute with the real
embedding, and the same normalized rational bank supplies nonnegative real
weights, positive survival values<=1 and all its real sparse moments. It
does not yet package the distinct-image bank as CM.FinitePositiveLaw or prove
the native parser/grouping implementation correct for all inputs.

Reuse the physical source helpers rather than introduce another real grouping
algorithm: positiveSupportPMF/_sum/_map and configurationBankPMF in
G4WholeProfileDetermination (sourcefb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09),
gridWeight/_moment/_eq_mapped_mass in G4ActualPositiveGridUniqueness
(sourceee5d196dc25a53b8d15957fcbaf9fdf13435b78eb03f8e66819d3f258f35b787).
Their source availability is distinct from a new combined-context compilation.
The existing finiteBankMoment p x k uses the same exponent k.choose2. The
accepted CM-T02 FinitePositiveLaw/moment is a separate receiver, whose typed
physical-PMF packaging remains explicit.

Mandatory practical input/output distinction: bank-derived moments are supplied
mathematical-law data. Measured moments need their own exact/error/provenance
contract. A physical YES needs the actual admitted graph/shared parameters and
all original rows. A certificate ROOT result, proposal failure, bounded search
NO or bank grouping does not establish unrestricted source YES/NO. Whole
configuration correlation stays in its ONE joint law. No product of site
marginals or independent per-level refit is authorized by this adapter.
