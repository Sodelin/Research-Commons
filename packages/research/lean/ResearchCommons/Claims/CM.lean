import CMSeparation
import CMRationalBank

/-! Typed exports of retained results. These aliases keep every original
hypothesis and conclusion; they add no proof premise or implementation claim. -/
noncomputable section
namespace ResearchCommons.Claims.CM
abbrev cap_five_separation := @Astra.CommonMoment.cm_t02_cap_five_separation
abbrev grouped_rational_law := @Astra.CommonMoment.RationalBank.fromGroupedRationals
abbrev grouped_rational_moments := @Astra.CommonMoment.RationalBank.fromGroupedRationals_moment
end ResearchCommons.Claims.CM
