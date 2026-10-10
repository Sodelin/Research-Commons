#!/usr/bin/env python3
"""Reproducible theorem-level map; source reads are not new compiler receipts."""
from pathlib import Path
import hashlib, json, re
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
records = []
def document_ref(path):
    return {'path':path, 'sha256':hashlib.sha256((ROOT / path).read_bytes()).hexdigest()}
def add(key, goal, obligation, status, sources=(), assumptions=(), supplies='', gaps=(), evidence=(), uses=()):
    refs = []
    for path, names in sources:
        p = ROOT / path
        body = p.read_bytes()
        for name in names:
            assert re.search(r'\b(?:theorem|lemma|def|abbrev|structure|instance)\s+' + re.escape(name.rsplit('.',1)[-1]) + r'\b', body.decode()), (path,name)
        refs.append({'path':path, 'sha256':hashlib.sha256(body).hexdigest(), 'declarations':list(names)})
    records.append({'id':key,'original_goal':goal,'original_obligation':obligation,
        'status':status,'providers':refs,'compatible_assumptions':list(assumptions),
        'reuse_supplies':supplies,'genuinely_remaining':list(gaps),'evidence':list(evidence),'cross_goal_dependencies':list(uses)})
base='research/'
add('G1-ORIGINAL','G1','Original contextual reduced decorated core and simultaneous all-n sharpness','inherited_formal_complete',[
 (base+'2026-10-04-dot-complete-original-g1-1549z/src/G1FullOriginalClassMasterAndSharpness.lean', ['G1FullOriginalClassMasterAndSharpness.actual_G1_original_class_master_with_all_n_sharpness'])],
 ['Finite binary rooted LSA/cut-child outer-labelled galled source with parallel original edge occurrences','At least four taxa','Complete unranked forest/register/current-root/context/history contract'],
 'Uniform core selected independently of source-law context; h<=2n-2,V<=6n-5,E<=8n-8 with sharp sources for every n>=4',
 ['Retained decoration word length is unbounded; this is not an exact-source witness-size bound for G3','Ranked internal merger-time experiments are not supplied'],
 [base+'2026-10-04-dot-complete-original-g1-1549z/certificate/fresh/SERIAL-BUILD-RECEIPT.json',base+'2026-10-10-dot-connected-53-qualified-certificate-0842z/README.md'])
add('G2-TIMED','G2','Natural and fixed-original-ID controlled complete timed all-panel projectivity','inherited_formal_complete',[
 (base+'2026-10-07-dot-g2-timed-endpoint-ordinary-integration-0941z/G2ActualTimedAllPanelLaw.lean', ['GProgram.G2.ActualTimedAllPanelLaw.actual_natural_complete_timed_all_panel_projectivity','GProgram.G2.ActualTimedAllPanelLaw.actual_controlled_complete_timed_all_panel_projectivity'])],
 ['Same finite original graph, copy labels, original parent registry and physical bank','Once-drawn natural original register; current live-owner routing','Literal pruning of absolute pair ages and complete unranked forest, including empty/singleton panels'],
 'Faithful same-clock sample deletion binds G5 ordinary triple observations and source-law composition',
 ['Fixed-time past/future statements are not arbitrary stopping-time termination theorems','No biological sequence-to-genealogy calibration follows'],
 [base+'2026-10-10-dot-g2-current-source-verification-0042z/README.md'], ['G1 physical prefix/context carriers'])
add('G3-GLOBAL','G3','Terminating exact same-source finite positive recognizer, including NO over every unknown finite source size','mathematically_open',[],
 ['Original finite rational/effectively real-algebraic observation input','One admitted source and shared original physical bank across all response rows'],
 'G1 core bounds, G6 finite-cell feasibility and G7 supplied-registry census give conditional bounded subproblems',
 ['Input-effective witness bound or complete unbounded NO coverage','Zero-distance exact positive attainment is not supplied by G6 closure approximation'],
 [base+'2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md'], ['G1-ORIGINAL','G6-AFFINE','G7-CENSUS'])
add('G3-LOCAL-NORMAL-BANK-OBSTRUCTION','G3','Local limit of a fixed finite critical-normal witness bank near one ordinary calibrated YES','independently_reviewed_hand_source_corollary',[],
 ['Original natural COMMON cap-seven eight-row calibration with all-core minimum-hybrid preservation','Fixed finite bank of nonzero critical-factor normals and uniformly bounded unrestricted head'],
 'Reuses the accepted Oct1 dyadic-Poisson closed-boundary exclusion and compact finite-count separation; new double sequence approaches one fixed rational ordinary YES with unbounded minimum original hybrid count and excludes the stated bank architecture',
 ['No Lean verification or executed RCF search','Target-dependent normal banks, discontinuous computable bounds and complete NO search remain unresolved','General coupled kernels, shared controls/registers and INDEPENDENT chronology are outside this transfer; full G3 remains open'],
 [document_ref(base+'2026-10-10-dot-g3-local-normal-bank-obstruction-1043z/LOCAL-NORMAL-BANK-OBSTRUCTION.md'),document_ref(base+'2026-10-10-dot-g3-local-normal-bank-obstruction-1043z/PRIOR-ATTRIBUTION-CLARIFICATION.md'),document_ref(base+'2026-10-10-dot-g3-local-normal-bank-obstruction-1043z/INDEPENDENT-SOURCE-PROVIDER-REVIEW.md'),document_ref(base+'2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md')], ['G3-GLOBAL'])
add('G4-RESTRICTED','G4','Finite observable rival length certificate in a supplied contracted positive-chain class','inherited_scoped_formal_complete',[
 (base+'2026-10-04-dot-verified-lean-825-0203z/package/baseline/Imported/G4TwoRootSourceStopping.lean',['G4TwoRootSourceStopping.observable_finite_length_certificate'])],
 ['PositiveChain target/rivals and declared rootedACladeResponse calibration','Supplied rival class C, antitone envelope U, all-rival RivalEnvelope and ArbitrarilySmall U'],
 'A positive target forces finite rival-chain length once an independently justified envelope tends to zero',
 ['The required uniform envelope does not cover arbitrary original unknown-size rivals by declaration','Original fixed-target full-menu G4 remains open'],
 [base+'2026-10-04-dot-verified-lean-825-0203z/package/README.md'])
add('G4-GLOBAL','G4','Target-derived finite full-menu forcing against all unknown-size strict positive original rivals, or fixed-target exact all-prefix counterexample','mathematically_open',[],
 ['One fixed admitted positive target','Rival may depend on prefix; target may not','Original legal final unranked observations and joint shared-source semantics'],
 'Existing cap and bounded-rival branches remain reusable at their exact hypotheses',
 ['All-rival localization/forcing or source-admitted fixed-target obstruction','Cap-dependent targets, signed-time identities and approximate collisions do not satisfy this contract'],
 [base+'2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md'])
add('G4-ORDINARY-OVERSHOOT-CERTIFICATE','G4','Finite exact Bernstein witness excluding a supplied ordinary-prefix overshoot','independently_reviewed_hand_source_corollary',[],
 ['Supplied finite private equal-arm target E_a B(t,g) K with t>0, interior g and positive finite tail','Supplied exact real-algebraic survival q_c in (0,exp(-a))','Rivals have a justified ordinary prefix at least c and positive projectively consistent current-root-exchangeable residual','Original-observation transfer additionally requires all ordered-pair natural COMMON calibration identities J and natural same-bank BOTH topology menu with the accepted forest decoder'],
 'Terminating enumeration of exact finite ordinary inverse blocks and strictly negative Bernstein moment inequalities; the original-taxon decoder learns the unknown completion law rather than observing hidden forest/root-count channels',
 ['Search and exact algebraic sign-certificate implementation are unexecuted','No uniform practical cap as c approaches a; arbitrary real c is not an effective input','Only an upper prefix constraint is supplied; smaller-prefix rivals, uncalibrated networks and INDEPENDENT-only menus remain unresolved; full G4 remains open'],
 [document_ref(base+'2026-10-10-dot-g4-ordinary-overshoot-certificate-1053z/ORDINARY-OVERSHOOT-MOMENT-CERTIFICATE.md'),document_ref(base+'2026-10-10-dot-g4-ordinary-overshoot-certificate-1053z/INDEPENDENT-REVIEW.md'),document_ref(base+'2026-10-10-dot-g4-ordinary-overshoot-certificate-1053z/CODEX-HANDOFF.md'),document_ref(base+'2026-10-09-dot-calibrated-tree-edge-reduction-1531z/CALIBRATED-ORIGINAL-TAXON-FOREST-DECODER.md')], ['G4-GLOBAL'])
add('G5-BINARY-M3','G5','Arbitrary-weight binary source triple full timed laws identify full normalized cluster and split unions','inherited_formal_complete',[
 (base+'2026-10-10-dot-g5-full-binary-m3-0209z/sources/G5M3NormalizedClusterSplitIdentification.lean',['GProgram.G5.M3NormalizedClusterSplitIdentification.m3_identifies_documented_full_cluster_split_unions'])],
 ['Finite binary temporal LSA directed multigraph; hybrid outgoing original edges are undirected bridges','Positive original and ancestral pair rates, interior source-specific inheritance','At least three original taxa; contemporaneous tips at same age','Each source retains its own COMMON/current-owner INDEPENDENT mechanism','Equality of ordinary hidden-register full timed genealogy laws on every original three-tip panel'],
 'Source-prefix support, posterior law, all-age cuts, safe chronology, exact blocks and original-label lifting are assembled; no fair-weight or planar premise is required',
 ['Co-occurrence family/full hidden graph/parameters are not identified','Finite binning is weaker than full timed-law equality','Categorical HG is a separate formal extension'],
 [base+'2026-10-10-dot-g5-full-binary-m3-0209z/CERTIFICATE.json'], ['G1 initialized physical prefix','G2 faithful same-clock all-panel law','Prior G5 posterior/frozen mixture','G6 original support/calendar providers'])
add('G5-HG','G5','Bounded-indegree categorical M_(k+1) hidden ambiguity recovery formal assembly','formalization_open',[],
 ['Categorical indegree<=k with strictly positive weights and its own source carrier'],
 'Binary M3 assembly is a reusable architecture, not the categorical proof instance',
 ['Categorical source route/position bound/safe support and decoder instance','No matching k+1 lower bound follows'],
 [base+'2026-10-10-dot-g5-full-binary-m3-0209z/README.md'])
add('G6-AFFINE','G6','Exact Boolean decision for one supplied original rational affine natural chart','inherited_formal_complete',[
 (base+'2026-10-09-dot-g6-proved-natural-cell-decision-1902z/StrictAffineElimination.lean',['UnifiedLean.G6.StrictAffineElimination.decideFeasible_correct','UnifiedLean.G6.StrictAffineElimination.real_feasible_iff_rational']),
 (base+'2026-10-09-dot-g6-proved-natural-cell-decision-1902z/NaturalCellAffineCompiler.lean',['UnifiedLean.G6.NaturalCellAffineCompiler.compileCell_correct','UnifiedLean.G6.NaturalCellAffineCompiler.decideOriginalCell_correct'])],
 ['Finite original graph','Supplied finite typed chronology/exposure/coin chart','Bijective BankVar layout including original ages, all physical inverse rates and original coins','One bank shared by every row; strict/non-strict rational rows'],
 'Complete real feasibility is equivalent to finite rational matrix decision at this fixed graph/chart',
 ['Automatic original graph admission and complete chart generation','Nonlinear exact observed-law equations and unknown-size source image'],
 [base+'2026-10-09-dot-g6-proved-natural-cell-decision-1902z/README.md'], ['G6 source-exact inverse-rate rewrite'])
add('G6-RATIONAL-WITNESS','G6','Construct a deterministic rational vector or decide real affine infeasibility','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6RationalAffineWitness.lean',['UnifiedLean.G6.RationalAffineWitness.solveRational_sound','UnifiedLean.G6.RationalAffineWitness.solveRational_complete','UnifiedLean.G6.RationalAffineWitness.solveList_eq_solveRational'])],
 ['Finite rational affine rows','Strict and weak inequalities, empty bound families, compatible weak singleton intervals'],
 'Executable back-substitution returns one exact vector; real feasibility iff a vector is returned; duplicate ordered list rows refine the same deterministic vector',
 ['Native projection/extremum algorithm equality remains separate','No original-source admission or unknown-size source search follows'],[], ['G6-AFFINE'])
add('G6-WITNESS','G6','Return and check an executable rational shared original-source bank','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6RationalAffineWitness.lean',['UnifiedLean.G6.RationalAffineWitness.solveRational_complete','UnifiedLean.G6.RationalAffineWitness.solveList_eq_solveRational']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6RationalNaturalCellWitness.lean',['UnifiedLean.G6.RationalNaturalCellWitness.solveOriginalCell_sound','UnifiedLean.G6.RationalNaturalCellWitness.solveOriginalCell_complete','UnifiedLean.G6.RationalNaturalCellWitness.solveOriginalCell_none_iff','UnifiedLean.G6.RationalNaturalCellWitness.checkedOriginalCellBank','UnifiedLean.G6.RationalNaturalCellWitness.checkedOriginalCellBank_rates','UnifiedLean.G6.RationalNaturalCellWitness.solveOriginalCellCertified_values'])],
 ['Same supplied original finite source/chart/layout as G6-AFFINE','Rational row vector, no independent segment coordinate declaration'],
 'Returned coordinates realize the actual original Calendar, PositivePairRates and HybridProbabilities; certified rational output erases to exactly the original solver vector',
 ['New sources require actual kernel-checked compilation','Does not supply a complete source search or positive representative proof'],[], ['G6-AFFINE'])
add('RUNTIME-POSITIVE-CHECKER','G6/Rust','Actual GParity wire certificate implies satisfaction of inherited real affine rows','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6WireAffineRefinement.lean',['UnifiedLean.G6.WireAffineRefinement.checkWitness_correct','UnifiedLean.G6.WireAffineRefinement.checkedWireWitness_real'])],
 ['Each parsed coefficient list has exactly n elements','Native checker verifies returned vector length','Rows decode to the inherited Row n without changing constants or strictness'],
 'List zipWith evaluation and successful native positive witness check are linked to actual typed row satisfaction',
 ['Native project/extrema algorithm equality and Rust universal implementation refinement remain separate','Differential byte tests are finite tested correspondence'],[], ['G6-RATIONAL-WITNESS'])
add('RUNTIME-NEGATIVE-CERTIFICATE','G6/Rust','Original-row weighted certificate excludes every real vector','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6AffineContradictionCertificate.lean',['UnifiedLean.G6.AffineContradictionCertificate.checked_excludes_real'])],
 ['Exactly one nonnegative rational multiplier per original row','Weighted coefficient vector zero','Weighted bound negative, or zero with a positively weighted strict original row'],
 'Sound independently checkable strict affine exclusion without trusting the projection trace',
 ['Matrix exclusion is source exclusion only for a source-faithful and complete admitted fixed chart'],[], ['G6-AFFINE'])
add('RUNTIME-NATIVE-NEGATIVE-CHECKER','G6/Rust','Actual native wire contradiction checker excludes every real vector of the original matrix','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6WireContradictionRefinement.lean',['UnifiedLean.G6.WireContradictionRefinement.checkContradiction_correct','UnifiedLean.G6.WireContradictionRefinement.checkedWireContradiction_excludes_real'])],
 ['Exact original-row coefficient lengths','One multiplier per original row','Native checker evaluates nonnegativity, zero normal, and negative bound or strict zero-bound use'],
 'Native list zip/fold/Boolean arithmetic is proved equivalent to the typed Valid certificate and thus excludes the inherited real matrix',
 ['Projection-trace production soundness and whole Rust refinement remain separate','A fixed matrix exclusion does not exclude unenumerated sources'],[], ['RUNTIME-NEGATIVE-CERTIFICATE'])
add('RUNTIME-CAP','G6/Rust','Exact native projection-cap answer versus UNKNOWN condition','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6WireAffineCapSemantics.lean',['UnifiedLean.G6.WireAffineCapSemantics.requiredCap','UnifiedLean.G6.WireAffineCapSemantics.solve_answered_iff','UnifiedLean.G6.WireAffineCapSemantics.solve_not_unknown'])],
 ['Actual deterministic native ordered list projection','Cap compared to every projected list size along the recursive matrix'],
 'Native SAT-or-UNSAT answer iff requiredCap <= cap; otherwise UNKNOWN; no unbounded-solver runtime premise is used',
 ['No small polynomial complexity bound','Answer arithmetic correctness comes from the independent certificate bridges'],[], [])
add('G6-ORDERED-SOURCE-COMPILER','G6/Rust','Effective complete source-registry list emission erases to the exact inherited compiler','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6NaturalCellOrderedCompiler.lean',['UnifiedLean.G6.NaturalCellOrderedCompiler.compileCellList_toFinset','UnifiedLean.G6.NaturalCellOrderedCompiler.nativeCompiledWitness_checked','UnifiedLean.G6.NaturalCellOrderedCompiler.nativeCompiledContradiction_excludes'])],
 ['Supplied typed RootedBinary','Complete effective lists of original edges, leaves, populations, hybrids, chronology IDs and exposure IDs','Bijective shared BankVar layout'],
 'Ordered rows.toFinset = compileCell; checked native positive/negative certificates transfer to the literal original source cell',
 ['Actual kernel compilation pending','General raw graph/parser admission and active-exposure chart completeness remain open'],[], ['G6-WITNESS','RUNTIME-NATIVE-NEGATIVE-CHECKER'])
add('G6-TYPED-NATIVE-FIXTURES','G6/Rust','Bind actual native CHART emission to the original typed two-tip source compiler','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6TwoTipChartFixture.lean',['UnifiedLean.G6.TwoTipChartFixture.source','UnifiedLean.G6.TwoTipChartFixture.layout','UnifiedLean.G6.TwoTipChartFixture.nativeRows_toFinset','UnifiedLean.G6.TwoTipChartFixture.nativeTypedRows_toFinset','UnifiedLean.G6.TwoTipChartFixture.nativeTypedWitnessBank'])],
 ['Concrete admitted two-tip graph root0 edges0:(0,1),1:(0,2), leaves1,2','Explicit bank ages0..2, original edge inverse rates3..4, ancestral inverse rate5','Literal empty9-row and typed17-row shared chart fixtures'],
 'Actual GParity.Chart.emitRows finite-set erasure equals inherited compileCell at this original typed source and layout',
 ['Actual kernel compilation pending','General graph/parser/active-exposure admission is not proved by a concrete fixture'],[], ['G6-ORDERED-SOURCE-COMPILER'])
add('G6-CELL-JOINT-LAW','G6','Completed joint forest/bin source law and TV bound within one full original calendar cell','inherited_scoped_formal_complete',[
 (base+'2026-10-10-dot-g6-completed-cell-tv-0258z/sources/G6CellCompletedBinPolynomial.lean',['UnifiedLean.G6.CellCompletedBinPolynomial.actual_cell_completed_bin_polynomial','UnifiedLean.G6.CellCompletedBinPolynomial.actual_cell_observed_bin_polynomial']),
 (base+'2026-10-10-dot-g6-completed-cell-tv-0258z/sources/G6ActualCellObservedTV.lean',['UnifiedLean.G6.ActualCellObservedTV.actual_cell_completed_observed_tv'])],
 ['Same finite original graph/copy carrier/readout and complete age/cut signature','Actual correlated survival/gamma bank; positive physical rates/interior inheritance','Finite bin alphabet; nonempty copy carrier where ancestral interpretation requires it'],
 'One exact rational polynomial table and coefficient-weighted TV bound for the actual naturally initialized completed same-record forest/bin law',
 ['Existence-selected coefficients are not yet an executable whole-table compiler','Not a uniform unknown-graph representative bound or target-image cloud'],
 [base+'2026-10-10-dot-g6-completed-cell-tv-0258z/README.md'], ['G7 whole actual polynomial epochs','G2 same-record observer'])
add('G6-PROTECTED-BINS','G6','Guarded register erasure and full forest/bin continuation','inherited_scoped_formal_complete',[
 (base+'2026-10-10-dot-g6-protected-bin-bridge-0912z/sources/G6ProtectedBinEndpoint.lean',['UnifiedLean.G6.ProtectedBinEndpoint.actual_constant_bin_forest_law','UnifiedLean.G6.ProtectedBinEndpoint.actual_word_exit_reconstructed']),
 (base+'2026-10-10-dot-g6-protected-bin-bridge-0912z/sources/G6UnrankedBinContinuation.lean',['UnifiedLean.G6.UnrankedBinContinuation.actual_guarded_unranked_bin_future'])],
 ['Fixed finite original graph and physical bank','Actual sorted calendar, original strict upper guard and tied boundary','One erased unranked causal interface retaining original IDs/nonprivate registers and all old bins'],
 'Earlier biological effect remains in forest; strict no-read makes later erased-register continuation exact',
 ['Normalized COMMON full-forest bigon mixture and positive bounded-chain realization inside protected cut segments','Cross-graph surgery, decoded-catalogue joint-bin transport, complete rational clouds and confidence stopping'],
 [base+'2026-10-10-dot-g6-protected-bin-bridge-0912z/README.md'], ['G1 current-root exit reconstruction','G2 finite-history transport','NaturalCalendarPastAdmission unused-seed independence'])
add('G6-COMMON-EXPOSURE','G6','Actual COMMON-bigon full retained-state and joint-context exposure transport','new_proof_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6CommonBigonExposureTransport.lean',['UnifiedLean.G6.CommonBigonExposureTransport.actual_constant_pulse_coLocated','UnifiedLean.G6.CommonBigonExposureTransport.actual_population_exposure_transport','UnifiedLean.G6.CommonBigonExposureTransport.actual_common_bigon_exposure_transport','UnifiedLean.G6.CommonBigonExposureTransport.actual_common_bigon_joint_context_transport']),
 (base+'2026-10-09-dot-g7-single-population-polynomial-2117z/G7SinglePopulationPolynomialKernel.lean',['GProgram.G7.SinglePopulationPolynomialKernel.actual_population_polynomial']),
 (base+'2026-10-04-dot-complete-original-g1-1549z/src/G1NonrootBigonKernel.lean',['G1NonrootBigonKernel.actual_bigon_program_kernel'])],
 ['Same original finite RootedBinary, sample assignment, parallel parent-edge occurrences and COMMON stored register','All current entering roots at the actual original hybrid; positive original calendars/rates','Equal selected original arm rho*duration on every actual entering support point','Arbitrary correlated prior and full forest/register/history exterior'],
 'Transfers the entire actual original Code law between physical banks at equal selected arm exposure, retaining every original forest/register/past field rather than only root-count survival',
 ['Compilation pending on compatible original provider closure','Identification of both arm laws with one normalized full-forest generator and guarded Bernoulli mixture','Positive bounded-chain realization, cross-graph source surgery and joint cut/bin transport'],
 [base+'2026-10-10-codex-lean-rust-parity/reuse/COMMON-BIGON-BRIDGE.md'], ['G1 original bigon/current-root transport','G7 full single-population polynomial','G6-PROTECTED-BINS'])
exposure_packet=base+'2026-10-10-dot-g6-forest-exposure-handoff-0941z/'
exposure_pins=json.loads((ROOT / (exposure_packet+'EXPOSURE-SOURCE-PINS.json')).read_text())
pin_sources=[]
for pin in exposure_pins:
    path='research/' + pin['url'].split('/research/',1)[1]
    assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == pin['sha256'], (pin['module'],path)
    pin_sources.append((path,[]))
add('G6-REVIEWED-FOREST-EXPOSURE','G6','Same finite original-source full forest row at equal occupied-population physical exposure','reviewed_hand_proof_formalization_pending',pin_sources,
 ['Fixed original graph/sample/copy carrier and admitted coLocated entering states with equal live/ancestor/live-genealogy forest key','Positive physical banks and nonnegative time','Joint bins retain same entering forest, carried old matrix, common tag and actual bin-word contracts','Natural COMMON mixture uses registry orientation and derived pre-pulse original unused-seed product','Future retains derived same exit IDs, nonprivate registers, common suffix and physical bank, strict guard and actual refinement/bin contracts'],
 'Newest reviewed source argument normalizes with the full population polynomial, couples actual uniformized choices/destinations/Poisson iterations, derives forest quotient lumpability before semigroup use, then uses the genuine original COMMON pulse and guard product',
 ['Hand/source review is not a Lean pass','Current saved COMMON draft compares the same entering Code and selected stored-bit arm; cross-arm forest-key identity still needs formal coupling/lumpability','Distinct INDEPENDENT/COMMON quantitative arguments, strictly positive reconstruction and full G6 clouds/stopping remain separate'],
 [exposure_packet+'EXPOSURE-HAND-PROOF.md',exposure_packet+'REVIEW-SCOPE.md',base+'2026-10-01-g6-effective-certification/PROOF.md',base+'2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md'],
 ['G6-COMMON-EXPOSURE','G6-PROTECTED-BINS','G1 current-root interface'])
records[-1]['governing_documents']=[document_ref(exposure_packet+'EXPOSURE-HAND-PROOF.md'),document_ref(exposure_packet+'EXPOSURE-SOURCE-PINS.json'),document_ref(base+'2026-10-01-g6-effective-certification/PROOF.md'),document_ref(base+'2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md')]
records[-1]['immutable_provider_pins']=exposure_pins
add('G6-WHOLE-EDGE-LIFT','G6/G7','Actual fixed-calendar whole-edge survival and original-coin physical image','new_proof_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6OriginalWholeEdgeSurvivalLift.lean',['UnifiedLean.G6.OriginalWholeEdgeSurvivalLift.ratesOfWholeEdgeSurvivals','UnifiedLean.G6.OriginalWholeEdgeSurvivalLift.lifted_whole_edge_survivals','UnifiedLean.G6.OriginalWholeEdgeSurvivalLift.lift_recovers_edge_rates','UnifiedLean.G6.OriginalWholeEdgeSurvivalLift.whole_edge_image_iff','UnifiedLean.G6.OriginalWholeEdgeSurvivalLift.whole_edge_and_coin_image_iff']),
 (base+'2026-10-04-dot-verified-lean-825-0203z/package/baseline/Imported/G4OrdinaryTripletReadout.lean',['G4OrdinaryTripletReadout.canonicalDuration_positive','G4OrdinaryTripletReadout.canonicalDuration_survival'])],
 ['Supplied actual original Calendar with every original edge duration strictly positive','Freely assignable independent positive original edge rates and one positive ancestral rate','Whole-edge survival coordinates and original hybrid probabilities strictly between zero and one'],
 'Constructs one literal original rates/coins bank on the same supplied calendar: rate_e=-log(z_e)/duration_e and ancestral rate one; all whole-edge coordinates are realized simultaneously and original edge rates are recovered at fixed calendar',
 ['Compilation pending on compatible original provider closure','No independent arbitrary cut/bin segment cube or arbitrary observation/probe/chart admission','Real logarithmic lift is not native rational witness extraction; calendar existence and complete source enumeration remain separate'],
 [base+'2026-10-10-codex-lean-rust-parity/reuse/WHOLE-EDGE-LIFT.md'], ['G4 canonical positive exponential duration','G6 original pair rates/calendar','G7 whole-source physical image consumer'])
records[-1]['governing_existing_candidate']={
 'path':base+'2026-10-10-dot-g7-pending-codex-recovery-0952z/latest/whole-edge/source-store/013d5d57a955e911ba808e4b1f91e5b63e8bdd4523bc1a09db64b5dfc2f73a69.lean',
 'sha256':'013d5d57a955e911ba808e4b1f91e5b63e8bdd4523bc1a09db64b5dfc2f73a69',
 'status':'UNCOMPILED_AFTER_EARLIER_FAILURE',
 'scope':'Constructive image overlaps this draft; stronger natural/all-original-controlled completed source-law retiming additionally depends on the uncompiled original whole-edge gathering chain.'}
add('G6-MASTER','G6','Effective target-preserving source-image clouds with both Hausdorff directions and robust statistical consumer','formalization_open',[],
 ['Accepted raw nonplanar binary temporal child-bridge source class','Declared finite natural bin profile and target fibre'],
 'G1 core/target transport and G7 nonplanar structural census are compatible first dependencies; finite supplied-chart witness extraction can provide local rational clouds',
 ['Positive full-forest chain compression/representative bound','Joint-bin decoded catalogue transport and exact empty/nonempty clouds','Confidence inversion, necessity and honest robust-fibre stopping'],
 [base+'2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md'], ['G1-ORIGINAL (use recovered nonplanar providers where matched)','G6-CELL-JOINT-LAW','G6-PROTECTED-BINS','G7-CENSUS'])
add('G7-CENSUS','G7/G6','Finite code census and decoder for a complete supplied original hybrid registry','inherited_scoped_formal_complete',[
 (base+'2026-10-09-dot-g7-original-registry-admission-1908z/sources/G7OriginalAdmission.lean',['GProgram.G7.OriginalAdmission.every_registered_source_survives_filter','GProgram.G7.OriginalAdmission.sourceOfValid','GProgram.G7.OriginalAdmission.decodedHybridMap_bijective','GProgram.G7.OriginalAdmission.decoded_parent_exact'])],
 ['Finite fixed taxon and complete original hybrid-ID registry','Binary rooted acyclic LSA/cut-child contract including distinct parallel parent occurrences'],
 'Executable complete nonplanar structural filter/decoder; exactly preserves original registered parent bits; suitable structural census for nonplanar G6',
 ['Original G7 outer-labelled planar/cofacial admission is absent, so filter is a superset there','Physical parameter cells and completed law transport must be supplied separately'],
 [base+'2026-10-09-dot-g7-original-registry-admission-1908z/README.md'])
add('G7-EPOCH','G7/G6','Actual full selected-forest polynomial table for one physical epoch','inherited_scoped_formal_complete',[
 (base+'2026-10-09-dot-g7-full-epoch-polynomial-2148z/G7FullEpochPolynomial.lean',['GProgram.G7.FullEpochPolynomial.actual_full_epoch_polynomial'])],
 ['Finite actual entering source snapshot/copy carrier and original population IDs','Original latent register conditioned on entering state','One positive bank and nonnegative epoch duration'],
 'Accepted semantic full-forest table SHA256 fc3a6ccca93b085f42b3b6b403094922cabc87b5b92b551a982f958438472ec2; not the later failed executable coefficient source a50c2612',
 ['Classical-choice selected table is not executable coefficient extraction','Physical shared whole-edge exposure/open-cube realization remains separate'],
 [base+'2026-10-09-dot-g7-full-epoch-polynomial-2148z/README.md'], ['G6 conditional joint-population split'])
recovery=base+'2026-10-10-dot-g7-pending-codex-recovery-0952z/'
add('G7-FULL-EPOCH-COEFFICIENTS','G7/G6/Rust','Executable sparse rational coefficient table for the actual full original-source forest epoch','new_derivative_compilation_pending',[
 (recovery+'latest/coefficients/source-store/6dabfdee6e47169a0135bc26523230213785338538c8179fc67d3cbc64cc3138.lean',['GProgram.G7.EffectiveSourceEnumeration.sourceValidDecidable','GProgram.G7.EffectiveSourceEnumeration.codeEnumeration']),
 (recovery+'latest/coefficients/source-store/df18fd3ffe02939b81fc062d48da60011a4724ae0d2cb9b9ea2e846e43b2e946.lean',['GProgram.G7.EffectivePopulationCoefficients.coefficients','GProgram.G7.EffectivePopulationCoefficients.actual_population_coefficients']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveFullEpochCoefficients.lean',['GProgram.G7.EffectiveFullEpochCoefficients.fullCoefficients_cons','GProgram.G7.EffectiveFullEpochCoefficients.fullCoefficients_actual','GProgram.G7.EffectiveFullEpochCoefficients.actual_full_epoch_coefficients'])],
 ['Explicit finite original graph/copy FinEnum carriers and original source-valid entering Code','Inherited ordered offDiag legal-pair half-rate recurrence','Ancestor-closed actual population panels, frozen original register and exact selected-view reassembly','One positive physical bank and nonnegative epoch duration'],
 'Separately attributed derivative of exact failed a50c2612 source adds one-layer normalization and explicit semantic induction arguments; all executable definitions and existing theorem statements preserved',
 ['Compilation pending in separately isolated recovered coefficients context; original enumeration/population historical individual passes do not certify the full chain','Full selected ownership/axiom audit and executable coefficient smoke remain required','Native unordered LAW quotient and universal Rust refinement remain separate'],
 [recovery+'README.md',recovery+'LATEST-CANDIDATE-STATUS.json',recovery+'attempts/20261010T025743.841574Z__00001-G7EffectiveFullEpochCoefficients/stdout',base+'2026-10-10-codex-lean-rust-parity/reuse/G7-FULL-EPOCH-REPAIR.json'],
 ['G7-EPOCH','G7 actual population split/reassembly'])
records[-1]['original_source_snapshot']={
 'path':recovery+'latest/coefficients/source-store/a50c2612cda2fd26238ee9a2435814cd679f7b23c6903abf81fed39357017b72.lean',
 'sha256':'a50c2612cda2fd26238ee9a2435814cd679f7b23c6903abf81fed39357017b72',
 'status':'FAILED_LATEST_EXACT_SOURCE',
 'diagnostic':'Deterministic default200000-heartbeat elaboration timeouts in cons proof lines296/310/313; no heartbeat increase in the derivative.'}
add('G7-ORIGINAL-WHOLE-EDGE-CANDIDATE','G7/G6','Whole-edge calendar gathering and actual natural/all-original-controlled completed survival chart','inherited_uncompiled_candidate_chain',[
 (recovery+'latest/whole-edge/source-store/f0c115252f9b62ad499959a2a0d28f884a981490a1cec23ae12f7e81ba4e4642.lean',['GProgram.G7.WholeEdgeExposureInvariant.actual_natural_completed_exposure_invariant','GProgram.G7.WholeEdgeExposureInvariant.actual_controlled_completed_exposure_invariant']),
 (recovery+'latest/whole-edge/source-store/013d5d57a955e911ba808e4b1f91e5b63e8bdd4523bc1a09db64b5dfc2f73a69.lean',['GProgram.G7.OriginalSurvivalCoverage.fixed_calendar_survival_image','GProgram.G7.OriginalSurvivalCoverage.actual_source_survival_chart'])],
 ['Same actual finite graph, original parent IDs/registry, natural coins and source mechanism','All original edge exposures equal on arbitrary strict comparison calendars and freely assignable positive edge banks','Ancestral completion uses actual root support; no timed/bin retiming is asserted'],
 'Existing stronger original candidate already contains fixed-calendar whole-edge cube realization and its intended complete natural/all-controlled source-law consumer; governing October1 frontier argument is reused rather than renamed as a new theorem',
 ['Whole-edge chain stops at OriginalEdgeOperators matrix type inference and PairAt/offDiag subtype normalization diagnostics','All subsequent candidate components and complete audit remain uncompiled/unrun','Constructive coordinate image alone does not imply whole chronological source-law equality'],
 [recovery+'source-notes/ALL-ORIGINAL-EDGE-EXPOSURE-PRESERVATION.md',recovery+'LATEST-CANDIDATE-STATUS.json',recovery+'attempts/20261010T025931.806556Z__00001-G7OriginalEdgeOperators/stdout',base+'2026-10-01-g7-continuous-design/PROOFS.md',base+'2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md'],
 ['G7-EPOCH','G1 actual frontier/context algebra','G2 source completion/control semantics'])
add('NATIVE-LAW-ORIGINAL-QUOTIENT','G7/G6/Rust','Native unordered ordinary forest kernel as pushforward of literal original ordered source coefficients','formalization_open',[],
 ['Actual admitted source-valid local Code with canonical live-only encoding and original sample/label embedding','All local Copy colocated in one original edge or ancestral population','Ordered source merger preserves first representative, ordered child graft, original locations/register; each orientation has half rate','Requested native forest coefficient is the sum over every literal Code destination in its explicit unordered canonical quotient fibre'],
 'Rust/design agree exact original recurrence and destination encoding; inherited population-split theorem supplies the required restricted-carrier architecture for mixed global frontiers',
 ['Proved original Code/encoding and ordered-to-unordered quotient transport','Actual inherited-definition native coefficient oracle and separately executed codegen receipt','Universal fibre-sum equality to LAW edgeKernel and label/population reassembly; finite examples do not establish it'],
 [base+'2026-10-10-codex-lean-rust-parity/design/POPULATION-REFINEMENT.md'],
 ['G7-FULL-EPOCH-COEFFICIENTS','G7 actual population split/reassembly'])
add('G7-EXECUTABLE-COEFFICIENT-SUPPORT','G7/G6/Rust','Zero actual population coefficients outside literal fuel-bounded original merger closure','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveCoefficientSupport.lean',['GProgram.G7.EffectiveCoefficientSupport.destinations','GProgram.G7.EffectiveCoefficientSupport.coefficients_zero_of_not_mem','GProgram.G7.EffectiveCoefficientSupport.coefficients_polynomial_zero_of_not_mem','GProgram.G7.EffectiveCoefficientSupport.actual_population_zero_of_not_mem'])],
 ['Any actual source-valid Code, arbitrary coefficient fuel and finite copy cardinality','Literal original Choice and merger with exact Code equality','Actual semantic zero-kernel conclusion additionally assumes all-Copy CoLocated in one original population'],
 'Direct recursion makes every raw rational coefficient zero off the original reflexive merger closure; polynomial zero then transports through the inherited actual population coefficient theorem',
 ['Fresh isolated checking and ownership/axiom audit remain pending','Code dictionary representation equality, quotient aggregation, complete normalized table extraction and universal Rust refinement remain separate'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/rust/SOURCE-POPULATION-ARGUMENT-20261010.md')], ['G7-FULL-EPOCH-COEFFICIENTS','NATIVE-LAW-ORIGINAL-QUOTIENT'])
add('G7-ENCODED-MERGER-SUPPORT','G7/G6/Rust','Actual encoding image contains the entire nonzero literal coefficient support of an encoded input','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EncodedMergerSupport.lean',['GProgram.G7.EncodedMergerSupport.Encoded','GProgram.G7.EncodedMergerSupport.merger_encoded','GProgram.G7.EncodedMergerSupport.destinations_encoded','GProgram.G7.EncodedMergerSupport.coefficients_zero_of_not_encoded','GProgram.G7.EncodedMergerSupport.encoded_dead_fields','GProgram.G7.EncodedMergerSupport.encoded_live_fields'])],
 ['Literal encodeActual image of an actually source-valid entering State','Arbitrary coefficient fuel and finite copy carrier; original Choice/merger and exact Code equality retained'],
 'Explicitly separates source validity after decoding from canonical encoding: all actual merger destinations remain encoded, nonencoded raw Code destinations have zero coefficients, active option fields are Some and dead fields None',
 ['Fresh checking and selected ownership/axiom audit remain pending','Full normalized dictionary/serialization equality, quotient linearity and universal Rust refinement remain separate'],
 [base+'2026-10-10-codex-lean-rust-parity/reuse/POPULATION-FIXTURE.md',base+'2026-10-10-codex-lean-rust-parity/design/POPULATION-REFINEMENT.md'], ['G7-EXECUTABLE-COEFFICIENT-SUPPORT','NATIVE-LAW-ORIGINAL-QUOTIENT'])
add('G7-ORIGINAL-POPULATION-NATIVE-FIXTURES','G7/G6/Rust','Execute inherited original population coefficients and literal unordered fibre sums on eight admitted fixtures','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalPopulationFixture.lean',['UnifiedLean.G7.OriginalPopulationFixture.initialState_sourceValid','UnifiedLean.G7.OriginalPopulationFixture.initialCode_coLocated','UnifiedLean.G7.OriginalPopulationFixture.carriedState_sourceValid','UnifiedLean.G7.OriginalPopulationFixture.carriedCode_coLocated','UnifiedLean.G7.OriginalPopulationFixture.coefficientTable','UnifiedLean.G7.OriginalPopulationFixture.quotientRows','UnifiedLean.G7.OriginalPopulationFixture.fixtureNamed'])],
 ['Checked actual original two-tip RootedBinary; all initial inputs constructed through inherited encodeActual','Zero through four local copies, original root/edge populations, injective fixture label embeddings and complete original vertex register','Carried nonminimum entering subtree is source-valid; no reachability from singleton tips is assumed','Tables query the unchanged inherited coefficient recurrence on deduplicated actual merger destinations'],
 'Saved native main implements exact design source_population_probe_v1 schema with literal Code rows plus sums over entire canonical global-label forest fibres; avoids full Code FinEnum scan',
 ['Source/proof compilation, full selected ownership/axiom audit and separate native code generation are pending','Eight-fixture independent Lean/Rust/oracle execution remains pending','Finite canonical serializer checks do not establish a universal Code-to-LAW quotient theorem'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/design/population_oracle.py'),base+'2026-10-10-codex-lean-rust-parity/design/POPULATION-REFINEMENT.md',base+'2026-10-10-codex-lean-rust-parity/reuse/POPULATION-FIXTURE.md'], ['G6-NATIVE-TWO-TIP-COMPILER','G7-EXECUTABLE-COEFFICIENT-SUPPORT','NATIVE-LAW-ORIGINAL-QUOTIENT'])
add('G7-COMPLETED-LAW','G7/G6','Natural/controlled original completed-calendar polynomial response chain','inherited_scoped_formal_complete',[
 (base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7CompletedCalendarPolynomial.lean',['GProgram.G7.CompletedCalendarPolynomial.actual_natural_completed_calendar_polynomial','GProgram.G7.CompletedCalendarPolynomial.actual_controlled_completed_calendar_polynomial'])],
 ['One finite original graph and parent registry','One original natural register draw and source-specific COMMON/current-owner INDEPENDENT routing','Shared actual segment-survival/gamma coordinates; fixed original-ID masks','Nonempty finite copy carrier for infinite completion interpretation'],
 'Original boundaries, natural initialization, physical epochs and same-source ancestral completion compose into a proved completed response law',
 ['Whole-edge/source-open-cube parameter ties are not independent by declaration','Executable coefficient extraction, cofacial admission and policy/rank/resource selection are not supplied'],
 [base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/README.md'], ['G7-EPOCH','G2 original-register/projectivity carriers'])
add('G7-POLICY-MASTER','G7','Effective finite-registry legal Pareto/policy or admitted response-consistent lower-certificate endpoint','formalization_open',[],
 ['Complete finite original registry','Original finite unranked readout menu and shared source bank','Exact-law reset/deletion-closed trajectory resource contract','Semialgebraic real action/sign/algebraic-selection model'],
 'Accepted hand characterization and source/compiler components remain the governing mathematics',
 ['Exact cofacial admission and executable rational polynomial whole-table extraction','Verified full-history shared-source Winning syntax and effective complete real QE','Action/lower-witness selection relative to actual history, resource-rank/deletion assembly and Pareto output'],
 [base+'2026-10-10-dot-g7-qe-interface-review-0026z/README.md',base+'2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md'], ['G7-CENSUS','G7-COMPLETED-LAW','G1 causal unranked context','G2 sample deletion'])
# Only a full successful fresh audit at the exact source hash promotes a new
# provider. Historical source reads and failed attempts never count as passes.
for certificate_name, accepted_status in [
    ('REUSE-CERTIFICATE.json', 'PASS_NEW_ARITHMETIC_REUSE_AND_WIRE_CHECKER'),
    ('TYPED-REUSE-CERTIFICATE.json', 'PASS_ORIGINAL_BANK_AND_NATIVE_TWO_TIP_COMPILER_FIXTURES')]:
    certificate = HERE.parent / 'lean' / certificate_name
    if not certificate.exists():
        continue
    cert = json.loads(certificate.read_text())
    if (cert.get('status') == accepted_status
        and not cert.get('owned_axioms') and not cert.get('nonstandard_axiom_rows')
        and not cert.get('missing_modules') and cert.get('kernel_checking')):
        compiled = {r['module']:r for r in cert.get('new_module_records', cert.get('records', [])) if r['exit_code'] == 0}
        for record in records:
            owned = [p for p in record['providers'] if '/reuse/sources/' in p['path']]
            if owned and all(Path(p['path']).stem in compiled
                and compiled[Path(p['path']).stem]['source_sha256'] == p['sha256'] for p in owned):
                record['status'] = 'new_kernel_checked_exact_source'
                record['evidence'].append('research/2026-10-10-codex-lean-rust-parity/lean/' + cert['evidence'] + '/RECEIPT.json')
                record['genuinely_remaining'] = [g for g in record['genuinely_remaining'] if 'compilation pending' not in g.lower()]
result={'schema':'commons-obligation-reuse-map-v1','contributor':'Codex / lean_reuse_recovery and lean_reuse_successor','created_utc':'2026-10-10','snapshot_kind':'source-read audit plus exact fresh kernel receipts where matched','source_hashes_checked':True,
 'global_constraints':['No sorry/admitted/custom axioms authorized','Inherited receipts remain attached only to their exact prior source/import context','Build/module counts do not establish master mathematical completion','Generic matrix/theorem validity does not supply biological measurement admission','Finite registry/rational chart exclusion is not unknown-size G3 NO coverage'],
 'obligations':records}
(HERE/'OBLIGATION-REUSE-MAP.json').write_text(json.dumps(result,indent=2)+'\n')
print(f'{len(records)} obligations; {sum(len(r["providers"]) for r in records)} hashed source references; all named source declarations found')
