#!/usr/bin/env python3
"""Reproducible theorem-level map; source reads are not new compiler receipts."""
from pathlib import Path
import gzip, hashlib, json, re
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
add('G4-SOURCE-UNIFORM-NEGATIVE-PRIMITIVE','G4','Sharp source-uniform chronological negative-part bound in actual equal-arm INDEPENDENT forest cells','independently_reviewed_hand_source_corollary',[],
 ['Actual current-root unmarked opaque-forest equal-arm B(t,g), ordinary pair-rate coalescence and complete pooling','One unchanged original IID routing bank, t>=0 and interior g','Arity n>=4 for the first nonzero primitive; fixed arity in shared-source countable limits','Natural BOTH observations additionally require the original same-bank COMMON calibration and calibrated decoder'],
 'Exact binomial two-merger integral and no-merger diagonal-ratio transport give prefix-weighted sum of negative primitive parts <=1/20, sharp via strict finite n=4 cells approaching the infinite-time limit',
 ['No Lean source/build or executed solver is supplied','Positive chronological reservoir layer or exact source-valid fixed-target rivals remain unresolved; full G4 is open','No arbitrary exchangeable projective kernel, retained-tag/timed-bin/controlled-register/arbitrary-graph extension or global G6 forest norm follows'],
 [document_ref(base+'2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z/CODEX-INTEGRATION-CONTRACT.md'),document_ref(base+'2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z/SOURCE-TWO-MERGER-TIME-INTEGRAL.md'),document_ref(base+'2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z/INDEPENDENT-NEGATIVE-PRIMITIVE-REVIEW.md'),document_ref(base+'2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z/PROVIDER-PINS.json')], ['G4-GLOBAL'])
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
add('G1-UNRANKED-SOURCE-LUMPABILITY','G1/G7/G6/Rust','Actual original step and epoch PMFs descend to the same unranked label/population/register view','inherited_scoped_formal_complete',[
 (base+'2026-10-04-dot-complete-original-g1-1549z/src/G1UnrankedSourceView.lean',['G1UnrankedSourceView.actual_unranked_population_blocks','G1UnrankedSourceView.actual_unranked_projected_merger']),
 (base+'2026-10-04-dot-complete-original-g1-1549z/src/G1UnrankedActualGenerator.lean',['G1UnrankedActualGenerator.actual_unranked_step_row_independent']),
 (base+'2026-10-04-dot-complete-original-g1-1549z/src/G1UnrankedActualEpoch.lean',['G1UnrankedActualEpoch.actual_unranked_time_kernel','G1UnrankedActualEpoch.actual_unranked_epoch_row_independent'])],
 ['Same actual finite N, sample, selected Copy panel and positive original rate bank','Equal full unranked selected subtree view, retaining each original population and SAME vertex register','Same nonnegative epoch duration; child-swap quotient preserves original labels and rooted topology'],
 'Existing original-source PMF lumpability erases implementation representatives and child orientations. This is reused as the source-side quotient premise rather than proved anew from a native formula',
 ['Native canonical global-label forest encoder agreement and explicit coefficient fibre sums remain separate','LAW divided-difference/history coefficient recurrence and injective restricted-carrier transport remain separate','Different original populations at equal exposure need an additional normalized forest-key bridge; the existing theorem keeps population IDs equal'],
 [base+'2026-10-04-dot-complete-original-g1-1549z/certificate/fresh/SERIAL-BUILD-RECEIPT.json'], ['G1-ORIGINAL','NATIVE-LAW-ORIGINAL-QUOTIENT'])
add('NATIVE-LAW-ORIGINAL-QUOTIENT','G7/G6/Rust','Native unordered ordinary forest kernel as pushforward of literal original ordered source coefficients','formalization_open',[],
 ['Actual admitted source-valid local Code with canonical live-only encoding and original sample/label embedding','All local Copy colocated in one original edge or ancestral population','Ordered source merger preserves first representative, ordered child graft, original locations/register; each orientation has half rate','Requested native forest coefficient is the sum over every literal Code destination in its explicit unordered canonical quotient fibre'],
 'Rust/design agree exact original recurrence and destination encoding; inherited G1 source PMF lumpability supplies representative/orientation erasure at equal full unranked population/register view, and the original population split supplies restricted-carrier architecture for mixed global frontiers',
 ['Proved original Code/encoding and ordered-to-unordered quotient transport','Actual inherited-definition native coefficient oracle and separately executed codegen receipt','Universal fibre-sum equality to LAW edgeKernel and label/population reassembly; finite examples do not establish it'],
 [base+'2026-10-10-codex-lean-rust-parity/design/POPULATION-REFINEMENT.md'],
 ['G7-FULL-EPOCH-COEFFICIENTS','G1-UNRANKED-SOURCE-LUMPABILITY','G7 actual population split/reassembly'])
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
add('G7-CONSTRUCTIVE-PANEL-JOIN','G7/G6/Rust','Construct an actual admitted global Code for every pair of admitted whole-copy panel indices','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7ConstructivePanelJoin.lean',['GProgram.G7.ConstructivePanelJoin.joinedState_valid','GProgram.G7.ConstructivePanelJoin.joinedState_sourceValid','GProgram.G7.ConstructivePanelJoin.joinCode_view','GProgram.G7.ConstructivePanelJoin.admitted_join_view','GProgram.G7.ConstructivePanelJoin.joinIndex_value']),
 (base+'2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceCopyCarrierTransport.lean',['UnifiedLean.Source.SourceCopyCarrierTransport.mapLabels_wellLabelled','UnifiedLean.Source.SourceCopyCarrierTransport.lifted_original_genealogy','UnifiedLean.Source.SourceCopyCarrierTransport.lifted_original_population']),
 (base+'2026-10-09-dot-g7-full-epoch-polynomial-2148z/G7FiniteForestReassembly.lean',['GProgram.G7.FiniteForestReassembly.viewIndex','GProgram.G7.FiniteForestReassembly.joinIndex'])],
 ['Any finite original Copy panel and its disjoint complement','Actually source-valid local Code states with the original graph and restricted original sample assignments','Literal tree-label subtype lifts, original locations and inherited LEFT-register join convention'],
 'Constructive joined state and encodeActual witness are intended to eliminate inherited index fallback on admitted local products, without scanning all Code states or equating decoded dead garbage',
 ['Fresh source checking and complete ownership/axiom audit pending','Same entering register and valid population factorization remain the inherited epoch-law premises','Normalized restricted coefficient table equality and full executable epoch extraction remain separate'],
 [base+'2026-10-10-codex-lean-rust-parity/reuse/CONSTRUCTIVE-PANEL-JOIN.md',base+'2026-10-10-codex-lean-rust-parity/design/EPOCH-REFINEMENT.md'], ['G7-FULL-EPOCH-COEFFICIENTS','G7-ENCODED-MERGER-SUPPORT'])
add('G7-SUPPORT-SELECTED-EXTRACTION','G7/G6/Rust','Support-only selected-row extraction equals the entire inherited rational populationSelected polynomial','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7PopulationSelectedSupport.lean',['GProgram.G7.PopulationSelectedSupport.populationSelectedSupport','GProgram.G7.PopulationSelectedSupport.polynomial_populationSelectedSupport','GProgram.G7.PopulationSelectedSupport.value_populationSelectedSupport','GProgram.G7.PopulationSelectedSupport.populationSelectedSupport_actual']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveFullEpochCoefficients.lean',['GProgram.G7.EffectiveFullEpochCoefficients.populationSelected','GProgram.G7.EffectiveFullEpochCoefficients.polynomial','GProgram.G7.EffectiveFullEpochCoefficients.populationSelected_actual'])],
 ['Any admitted original Code, finite original Copy carrier and complete FinEnum providers','Exact deduplicated original Choice/merger closure at copy-cardinality fuel','Rational polynomial identity requires no physical-bank or CoLocated premise; actual-kernel interpretation additionally requires all-Copy CoLocated'],
 'The accepted outside-support raw-zero theorem removes every omitted Code term from the complete selected-view pushforward, proving exact polynomial equality independent of list ordering and raw duplicate monomials',
 ['Fresh source checking and complete ownership/axiom audit pending','General sparse normalization/serializer equality and universal Rust refinement remain separate','Full epoch row-product support and selected-index extraction correspondence remain separate'],
 [base+'2026-10-10-codex-lean-rust-parity/reuse/SUPPORT-SELECTED-EXTRACTION.md',base+'2026-10-10-codex-lean-rust-parity/design/EPOCH-REFINEMENT.md'], ['G7-EXECUTABLE-COEFFICIENT-SUPPORT','G7-FULL-EPOCH-COEFFICIENTS','G7-CONSTRUCTIVE-PANEL-JOIN'])
add('G7-EFFECTIVE-PANEL-JOIN','G7/G6/Rust','Executable panel constructor refines inherited selected-index join on actual local Code witnesses','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectivePanelJoin.lean',['GProgram.G7.EffectivePanelJoin.joinedStateEffective','GProgram.G7.EffectivePanelJoin.joinedCode','GProgram.G7.EffectivePanelJoin.joinedSelected_eq'])],
 ['Actually admitted local original Code witnesses on a finite copy panel/complement','Original restricted sample maps, ordered trees, populations and inherited LEFT-register convention'],
 'Pure constructor and original encodeActual/project refine inherited joinSelected without extracting a Prop witness or scanning Code',
 ['Fresh checking and complete audit pending','Full epoch product extraction and universal Rust refinement remain separate'],
 [base+'2026-10-10-codex-lean-rust-parity/reuse/CONSTRUCTIVE-PANEL-JOIN.md'], ['G7-CONSTRUCTIVE-PANEL-JOIN','G7-FULL-EPOCH-COEFFICIENTS'])
add('G7-SPARSE-ROW-PRODUCTS','G7/G6/Rust','Exact selected polynomial of supplied literal-row products equals the finite selected-key fibre sum','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7SparseRowProducts.lean',['GProgram.G7.SparseRowProducts.readRows','GProgram.G7.SparseRowProducts.multiplyRows','GProgram.G7.SparseRowProducts.polynomial_product','GProgram.G7.SparseRowProducts.polynomial_read_multiplyRows_partition'])],
 ['Explicit projected literal join equals the inherited selected-key join','All supplied literal rows in every selected-key fibre contribute; repeated keys are summed'],
 'Pure list row products admit a universal rational polynomial pushforward identity; no complete finite Code carrier is enumerated',
 ['Fresh checking and complete audit pending','Specific full original epoch consumer and normalized serializer/refinement remain separate'],
 [base+'2026-10-10-codex-lean-rust-parity/reuse/FULL-EPOCH-SUPPORT.md'], ['G7-SUPPORT-SELECTED-EXTRACTION','G7-EFFECTIVE-PANEL-JOIN'])
add('G7-FULL-EPOCH-SUPPORT','G7/G6/Rust','Support-only literal whole-epoch rows refine unchanged inherited fullCoefficients and actual epoch law','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7FullEpochSupport.lean',['GProgram.G7.FullEpochSupport.fullRows','GProgram.G7.FullEpochSupport.fullRows_register','GProgram.G7.FullEpochSupport.polynomial_fullRows','GProgram.G7.FullEpochSupport.epochRows_actual'])],
 ['Any actual admitted original entering Code and finite original copy carrier','Whole current-population ancestor fibres, original restricted sample maps and subtype label lifts','Entire original entering register preserved by every row witness','Full polynomial identity is algebraic; physical fullRows law retains ActiveIn, positive original bank and nonnegative duration'],
 'New executable support lists and constructive Code joins are intended to give exact whole selected-view polynomial output without complete Code/selected-index scans',
 ['Fresh checking and complete audit pending','Eight ordinary and separately typed parallel mixed epoch compiled evaluator comparisons pending','General normalized dictionary/serializer and universal Rust refinement remain open'],
 [base+'2026-10-10-codex-lean-rust-parity/reuse/FULL-EPOCH-SUPPORT.md',base+'2026-10-10-codex-lean-rust-parity/design/EPOCH-REFINEMENT.md'], ['G7-SPARSE-ROW-PRODUCTS','G7-SUPPORT-SELECTED-EXTRACTION','G7-EFFECTIVE-PANEL-JOIN','G7-FULL-EPOCH-COEFFICIENTS'])
add('G7-RANK-COMPRESSION-REPAIR','G7','Pointwise-total exact-law policy has a finite rank bound on physical informative calls','new_elaboration_derivative_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7ExactLawRankCompression.lean',['GProgram.G7.ExactLawRankCompression.redundant_response_unique','GProgram.G7.ExactLawRankCompression.first_informative','GProgram.G7.ExactLawRankCompression.pointwise_total_strategy_has_finite_informative_horizon'])],
 ['Original affine response representation, finite-dimensional base coefficient space','Pointwise CorrectRun on actual admitted sources; deletion-closed legality and original path update'],
 'Explicit include affine scopes restore declared proof premises dropped by section-variable inference; executable definitions and resources preserved',
 ['Fresh checking and complete audit pending','Effective simulation, span testing, complete QE/CAD and G7 Pareto extraction remain separate'],
 [base+'2026-10-10-codex-lean-rust-parity/reuse/G7-RANK-COMPRESSION-REPAIR.json'], ['G7-POLICY-MASTER'])
add('G7-ORIGINAL-FAMILY-CARRIER-COMPOSITION','G7','Actual positive-support programme resources and census-derived response-preserving original carrier assembly','inherited_exact_candidates_compilation_pending',[
 (recovery+'latest/semantic/source-store/1a95edf6b4a0e361ccc053531fd24de4de45b6253a139b266e68d282c3fbecd5.lean',['GProgram.G7.OriginalFamilyStrategy.actual_programme_response_linear','GProgram.G7.OriginalFamilyStrategy.original_programme_legal_deletion','GProgram.G7.OriginalFamilyStrategy.actual_total_original_strategy_bounded_winning','GProgram.G7.OriginalFamilyStrategy.actual_losing_budget_excludes_total_policy']),
 (recovery+'latest/semantic/source-store/78f22f5917212683b4429d446231907bb8694b17b58d9234cd869eabd8099c6e.lean',['GProgram.G7.OriginalCarrierCoverage.every_original_row_has_fixed_carrier_response','GProgram.G7.OriginalCarrierCoverage.every_original_programme_has_fixed_carrier_response']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalCarrierCoverage.lean',['GProgram.G7.OriginalCarrierCoverage.every_original_row_has_fixed_carrier_response','GProgram.G7.OriginalCarrierCoverage.every_original_programme_has_fixed_carrier_response'])],
 ['Complete original hybrid registry and same original graph/calendar/positive bank across all reset rows','Literal pre-source PMF programme randomization, finite output channels and positive support costs','Pointwise total exact-law policy; union-site/row/call path budget preserved under sublist deletion','Exact original census carrier equivalences, no padding or refitted bank'],
 'Existing compatible semantic consumers derive linear responses and physical path costs, compose F1 rank horizon, and preserve every actual original row/programme on exact finite carriers; reuse these proofs before creating another strategy argument',
 ['Repair rank section elaboration and compile/audit complete original semantic191 context','Effective syntax, cofacial admission, independent whole-edge coverage and real QE/selection/Pareto producer remain separate'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/G7-CLOSURE-AUDIT-20261010.md'),recovery+'source-notes/FORMAL-COVERAGE.md'], ['G7-RANK-COMPRESSION-REPAIR','G7-CENSUS','G7-COMPLETED-LAW','G7-POLICY-MASTER'])
add('G7-ORIGINAL-EPOCH-NATIVE-FIXTURES','G7/G6/Rust','Eight ordinary and ninth actual parallel-source whole selected-view epoch comparisons','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalEpochFixture.lean',['UnifiedLean.G7.OriginalEpochFixture.twoEdgeState_sourceValid','UnifiedLean.G7.OriginalEpochFixture.edgeAncestralState_sourceValid','UnifiedLean.G7.OriginalEpochFixture.carriedNodeState_sourceValid','UnifiedLean.G7.OriginalEpochFixture.fixtureJson','UnifiedLean.G7.OriginalEpochFixture.fixtureNamed']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalEpochFixtureMain.lean',['main']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalParallelEpochFixture.lean',['UnifiedLean.G7.OriginalParallelEpochFixture.graphCode_valid','UnifiedLean.G7.OriginalParallelEpochFixture.graphCode_registryValid','UnifiedLean.G7.OriginalParallelEpochFixture.parentOccurrence_exact','UnifiedLean.G7.OriginalParallelEpochFixture.initialState_sourceValid','UnifiedLean.G7.OriginalParallelEpochFixture.fixture']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalParallelEpochFixtureMain.lean',['main'])],
 ['Actual encodeActual entering images and complete original sample/label embeddings','Complete ordered selected genealogy/population/full-register output and literal Code witnesses','Separately typed rooted binary LSA parallel parent occurrences E2/E3, complete original registry false=2/true=3','Exact sparse support-only baseline polynomial_fullRows, no complete four-copy Code enumeration'],
 'Source-valid empty/singleton/mixed edge/ancestral/node exterior/carried/permuted/parallel contexts instantiate the exact original sparse epoch baseline and serialize every selected-view fibre',
 ['Fresh separate source/audit checks and actual compiled-evaluator runs pending','Independent nine-context Lean/Rust/whole-generator comparison pending','General normalization/serializer correctness and universal Rust refinement remain open'],
 [base+'2026-10-10-codex-lean-rust-parity/design/EPOCH-REFINEMENT.md',base+'2026-10-10-codex-lean-rust-parity/reuse/FULL-EPOCH-SUPPORT.md'], ['G7-FULL-EPOCH-SUPPORT','G7-CENSUS','G6-NATIVE-TWO-TIP-COMPILER'])
add('G7-EXECUTABLE-BOUNDARY-COEFFICIENTS','G7/G6/Rust','Conditional original current-owner and stored-register boundary sparse rows refine inherited polynomial readouts','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveBoundaryCoefficients.lean',['GProgram.G7.EffectiveBoundaryCoefficients.pulseCodeEffective_eq','GProgram.G7.EffectiveBoundaryCoefficients.exitCodeEffective_eq','GProgram.G7.EffectiveBoundaryCoefficients.polynomial_pulseRows','GProgram.G7.EffectiveBoundaryCoefficients.polynomial_commonRows','GProgram.G7.EffectiveBoundaryCoefficients.pulseRows_register','GProgram.G7.EffectiveBoundaryCoefficients.pulseRows_actual']),
 (recovery+'source-store/f447e7ad6c52ab2a16781fb4671e33eadf508309789f2f0046f2765237efcf4c.lean',['GProgram.G7.OriginalBoundaryPolynomial.coinPolynomial','GProgram.G7.OriginalBoundaryPolynomial.pulsePolynomial','GProgram.G7.OriginalBoundaryPolynomial.actual_pulse_polynomial'])],
 ['Actual rooted binary graph, admitted entering Code and genuine original hybrid-parent pair','Exactly current AtNode live owners, each complete ancestral fibre shares one pulse coin','Original gamma is probability true/parent1; COMMON uses entering stored bit and conditional constant1','Complete entering register, genealogy, ancestor and original location/edge IDs retained'],
 'New executable literal witness and sparse coefficient composition reuses unchanged inherited boundary polynomial; no reproof of source boundary projectivity and no full Code/selected-index enumeration',
 ['Fresh source/audit checks and twelve typed boundary evaluator comparisons pending','General normalization/serialization and universal Rust refinement remain open','Finite word/calendar legal-order and once-drawn initialization/completion coefficient composition remain separate'],
 [base+'2026-10-10-codex-lean-rust-parity/design/BOUNDARY-REFINEMENT.md',base+'2026-10-10-codex-lean-rust-parity/design/SOURCE-PARENT-ORIENTATION.md'], ['G7-SPARSE-ROW-PRODUCTS','G7-FULL-EPOCH-SUPPORT','G2-TIMED','G7-COMPLETED-LAW'])
add('G7-EXECUTABLE-INITIALIZATION-COEFFICIENTS','G7/G6/Rust','Executable once-drawn complete original hybrid register mixture refines unchanged initialPolynomial','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveInitializationCoefficients.lean',['GProgram.G7.EffectiveInitializationCoefficients.originalRegisterEffective_eq','GProgram.G7.EffectiveInitializationCoefficients.initialCodeEffective_eq','GProgram.G7.EffectiveInitializationCoefficients.polynomial_initialRows','GProgram.G7.EffectiveInitializationCoefficients.initialRows_actual']),
 (base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7OriginalInitializationPolynomial.lean',['GProgram.G7.OriginalInitializationPolynomial.registerPolynomial','GProgram.G7.OriginalInitializationPolynomial.initialPolynomial','GProgram.G7.OriginalInitializationPolynomial.actual_original_initial_polynomial'])],
 ['Same original graph, hybrid carrier and sample map; actual encodeActual source initialization','True is original parent1, nonhybrid register bits false, every hybrid register drawn once including empty Copy','Explicit shared variable embedding; physical evaluation substitutes the same original gamma assignment'],
 'Pure finite register/initial-Code support targets exact rename of the unchanged original initialization polynomial without a whole Code or selected-index scan',
 ['Revised initialization kernel/audit check pending; accepted boundary dependency remains frozen','Concrete natural word composition, normalization/serializer correctness and universal Rust refinement remain separate'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/WORD-PROVIDER-READBACK-20261010.md'),base+'2026-10-10-codex-lean-rust-parity/design/WORD-REFINEMENT.md'], ['G7-EXECUTABLE-BOUNDARY-COEFFICIENTS','G7-COMPLETED-LAW'])
add('G7-SPARSE-WORD-COMPOSITION','G7/G6/Rust','Finite literal dependent-row composition for exact polynomial or shared-bank physical original words','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7SparseWordComposition.lean',['GProgram.G7.SparseWordComposition.bindRows','GProgram.G7.SparseWordComposition.followRows','GProgram.G7.SparseWordComposition.polynomial_followRows','GProgram.G7.SparseWordComposition.polynomial_original_word','GProgram.G7.SparseWordComposition.actual_followRows','GProgram.G7.SparseWordComposition.evaluated_original_word']),
 (base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7SymbolicProgramPolynomial.lean',['GProgram.G7.SymbolicProgramPolynomial.wordPolynomial','GProgram.G7.SymbolicProgramPolynomial.actual_source_word_polynomial','GProgram.G7.SymbolicProgramPolynomial.actual_natural_word_polynomial']),
 (base+'2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceProgramTransport.lean',['UnifiedLean.Source.SourceProgramTransport.actual_program_step_projection','UnifiedLean.Source.SourceProgramTransport.actual_source_program_projection'])],
 ['Complete literal conditional support lists, actual admitted Code witnesses, exact coefficient products and full destination fibre sums','Exact word coefficient theorem requires exact per-step selected-table coefficient identity','Separate physical theorem requires actual per-step law and one shared positive original rate bank, nonnegative slot durations, gamma and mode vector'],
 'Executable bind/follow recurrence visits finite supplied supports; existing actual source projection transports the physical word law while coefficient identity retains its stronger explicit premise',
 ['Fresh kernel/audit checking pending','Concrete original node/slot/natural initialization consumer remains to be composed','Chosen epochTable/representative polynomial uniqueness is an explicit gap; shared-slot physical evaluation is not an arbitrary survival cube','General normalized dictionary/serializer correctness, runtime cap semantics and universal Rust refinement remain open'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/WORD-PROVIDER-READBACK-20261010.md'),document_ref(base+'2026-10-10-codex-lean-rust-parity/design/WORD-CHOSEN-TABLE-OBLIGATION-20261010T1240Z.md')], ['G7-SPARSE-ROW-PRODUCTS','G7-FULL-EPOCH-SUPPORT','G7-EXECUTABLE-INITIALIZATION-COEFFICIENTS','G7-COMPLETED-LAW'])
add('G7-SUPPORT-ANCESTRAL-COMPLETION','G7/G6/Rust','Support-only exact rational rows for actual infinite ancestral completion','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveAncestralCompletion.lean',['GProgram.G7.EffectiveAncestralCompletion.kernelExpr_eq_ancestral','GProgram.G7.EffectiveAncestralCompletion.constantCoefficients','GProgram.G7.EffectiveAncestralCompletion.readRational_ancestral','GProgram.G7.EffectiveAncestralCompletion.rationalRows_actual','GProgram.G7.EffectiveAncestralCompletion.readRational_eq_completionRational','GProgram.G7.EffectiveAncestralCompletion.completionRows_actual']),
 (base+'2026-10-09-dot-g7-actual-ancestral-polynomial-2101z/G7AncestralPolynomialKernel.lean',['GProgram.G7.AncestralPolynomialKernel.kernelExpr','GProgram.G7.AncestralPolynomialKernel.ancestralPolynomial']),
 (base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7AncestralRationalCompletion.lean',['GProgram.G7.AncestralRationalCompletion.actual_completion_at_zero','GProgram.G7.AncestralRationalCompletion.actual_completion_rational']),
 (base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7SelectedCompletionPolynomial.lean',['GProgram.G7.SelectedCompletionPolynomial.actual_source_completion_projection','GProgram.G7.SelectedCompletionPolynomial.actual_selected_completion_rational'])],
 ['Algebraic recurrence-name equality at arbitrary fuel and actual admitted Code','Actual completion statements require nonempty Copy, full all-copy AncestralRoot support and positive original rate bank','Complete ordered selected genealogy/location/full original register retained; no additional survival variable'],
 'Reuses identical inherited ordered-half-rate recurrence bodies, accepted outside-support zero and the genuine original completion limit to identify exact rational sparse fibre rows with completionKernel and unchanged completionRational',
 ['Fresh kernel checking and complete audit pending','Six direct original rational completion fixtures and whole finite-word completion composition remain pending','General native encoding/normalization refinement and chosen epoch-table coefficient identity remain separate'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/design/WORD-COMPLETION-EXTENSION-20261010T1300Z.md'),document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/WORD-PROVIDER-READBACK-20261010.md')], ['G7-EXECUTABLE-COEFFICIENT-SUPPORT','G7-SUPPORT-SELECTED-EXTRACTION','G7-COMPLETED-LAW'])
add('G7-ORIGINAL-COMPLETION-NATIVE-FIXTURES','G7/G6/Rust','Six direct source-valid complete rational ancestral-root selected-law controls','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalCompletionFixture.lean',['UnifiedLean.G7.OriginalCompletionFixture.flatState_sourceValid','UnifiedLean.G7.OriginalCompletionFixture.encoded_ancestral','UnifiedLean.G7.OriginalCompletionFixture.carriedState_sourceValid','UnifiedLean.G7.OriginalCompletionFixture.carriedCode_ancestral','UnifiedLean.G7.OriginalCompletionFixture.fixtureNamed']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalCompletionFixtureMain.lean',['main'])],
 ['Actual encodeActual image on the original typed two-tip source','Nonempty1..4 Copy, all-copy AncestralRoot and complete conditional registerTFT','Ordered carried subtree/nonminimum representative and injective permuted global label controls'],
 'Runs only actual merger-support coefficient lists, sums exact rational coefficient0 over every complete selected fibre, and retains a literal witness with nonzero constant contribution',
 ['Fresh separate source/audit and compiled-evaluator comparisons pending','General native encoding/normalization refinement and full word wrapper/work correspondence remain separate'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/design/WORD-COMPLETION-EXTENSION-20261010T1300Z.md'),document_ref(base+'2026-10-10-codex-lean-rust-parity/design/evidence/word-completion-fixture-freeze-1/INVENTORY.json')], ['G7-SUPPORT-ANCESTRAL-COMPLETION','G7-ORIGINAL-EPOCH-NATIVE-FIXTURES'])
add('G7-SINGLE-EPOCH-TABLE-IDENTITY','G7/G6/Rust','Entire effective sparse epoch polynomial equals the unchanged chosen selected epochTable before word composition','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7SelectedEpochTableUniqueness.lean',['GProgram.G7.SelectedEpochTableUniqueness.survival_inverseLogRates','GProgram.G7.SelectedEpochTableUniqueness.polynomial_eq_of_single_epoch_evaluations','GProgram.G7.SelectedEpochTableUniqueness.polynomial_epochRows_eq_epochTable','GProgram.G7.SelectedEpochTableUniqueness.polynomial_epochRows_representative_independent','GProgram.G7.SelectedEpochTableUniqueness.renamed_epochRows_eq_epochTable']),
 ('/workspace/dependencies/mathlib4/Mathlib/Algebra/MvPolynomial/Funext.lean',['MvPolynomial.funext_set']),
 (base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7SelectedKernelPolynomial.lean',['GProgram.G7.SelectedKernelPolynomial.epochTable','GProgram.G7.SelectedKernelPolynomial.actual_selected_epoch_table'])],
 ['Every actual admitted finite original Code and same complete selected genealogy/location/register fibre','At one physical epoch time1 independently positive original pair rates -log(x_i) realize x_i in(0,1)','Injective rational-to-real coefficient map and exact existing source-time kernel projection','Slot rename may identify/repeat coordinates only after the single-epoch polynomial identity'],
 'Reuses exact Mathlib infinite-box polynomial uniqueness and existing original PMF projectivity to identify the entire rational coefficient table and prove admitted-representative independence',
 ['Fresh kernel checking and complete audit pending','Concrete original node/exit table coefficient binding and exact word/natural/completed consumer still need composition','General native encoding/normalization refinement remains separate; shared multi-slot calendar evaluations do not form an independent cube'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/EXACT-PROVIDER-LEADS-20261010T1315Z.json'),document_ref(base+'2026-10-10-codex-lean-rust-parity/design/WORD-CHOSEN-TABLE-OBLIGATION-20261010T1240Z.md')], ['G7-FULL-EPOCH-SUPPORT','G7-SPARSE-WORD-COMPOSITION','G7-COMPLETED-LAW'])
add('G7-ORIGINAL-BOUNDARY-PHASE-PERMUTATION','G7/G6/Rust','Original full-Code calendar law is invariant under finite reordering within each boundary phase','inherited_scoped_formal_complete',[
 (base+'2026-10-09-dot-g7-natural-calendar-relabelling-1958z/G7BoundaryPhasePermutation.lean',['GProgram.G7.BoundaryPhasePermutation.program_append','GProgram.G7.BoundaryPhasePermutation.exit_phase_perm','GProgram.G7.BoundaryPhasePermutation.node_phase_perm']),
 (base+'2026-10-09-dot-g7-natural-calendar-relabelling-1958z/G7BoundaryExitCommutation.lean',['GProgram.G7.BoundaryExitCommutation.exit_code_commute']),
 (base+'2026-10-09-dot-g7-natural-calendar-relabelling-1958z/G7NodeActions.lean',['GProgram.G7.NodeActions.kernels_commute'])],
 ['Same original graph, admitted Code, positive bank, original parent registry/gamma/COMMON assignment','Lists are permutations within the exit phase or within the original node-entry phase','Exit and entry phases retain their original order'],
 'Existing exact sourceProgram PMF equalities already prove same-phase kernel commutation/permutation; sorted original-ID execution needs a finite list Perm certificate and word composition, not a new source kernel theorem',
 ['Effective sorted enumeration permutation/calendar-date/refinement composition remains separate','Entire coefficient identity must use the per-step coefficient bridges; physical calendar evaluation alone does not prove arbitrary shared-slot coefficients'],
 [base+'2026-10-10-codex-lean-rust-parity/lean/SEMANTIC-RANK-RECOVERY-CERTIFICATE.json',document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/WORD-PROVIDER-READBACK-20261010.md')], ['G7-SPARSE-WORD-COMPOSITION','G7-COMPLETED-LAW'])
add('G7-CONCRETE-ORIGINAL-NODE-COEFFICIENTS','G7/G6/Rust','Finite original node resolver and entire sparse node/exit identities with inherited selected tables','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveNodeCoefficients.lean',['GProgram.G7.EffectiveNodeCoefficients.incomingEdgeEffective_eq','GProgram.G7.EffectiveNodeCoefficients.polynomial_nodeRows','GProgram.G7.EffectiveNodeCoefficients.polynomial_eq_of_gamma_evaluations','GProgram.G7.EffectiveNodeCoefficients.polynomial_nodeRows_eq_nodeTable','GProgram.G7.EffectiveNodeCoefficients.polynomial_exitRows_eq_exitTable']),
 (base+'2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceBoundaryProjection.lean',['UnifiedLean.Source.SourceBoundaryProjection.actual_boundary_projection'])],
 ['Every admitted original entering Code and complete selected genealogy/location/register fibre','Finite incoming edge filter/head equals inherited arbitrary selector only at actual proven indegree-one nodes','Original current-owner INDEPENDENT gamma is true/parent1; stored COMMON bit retained','Original boundary projection and polynomial uniqueness on the original-gamma open box'],
 'New concrete composition reuses checked pulse/common/pure rows and already proved source boundary projectivity to supply inherited nodeTable/exitTable coefficient identities',
 ['Fresh prerequisite and root kernel/audit checks pending','Concrete word/natural/calendar composition and universal native encoding/normalization remain separate'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/WORD-PROVIDER-READBACK-20261010.md')], ['G7-EXECUTABLE-BOUNDARY-COEFFICIENTS','G7-EXECUTABLE-INITIALIZATION-COEFFICIENTS','G7-SPARSE-WORD-COMPOSITION'])
add('G7-CONCRETE-ORIGINAL-WORD-COEFFICIENTS','G7/G6/Rust','Actual interval/exit/enter sparse rows identify entire inherited wordPolynomial and naturalWordPolynomial','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveWordCoefficients.lean',['GProgram.G7.EffectiveWordCoefficients.polynomial_renameSparse','GProgram.G7.EffectiveWordCoefficients.polynomial_stepRows','GProgram.G7.EffectiveWordCoefficients.polynomial_wordRows','GProgram.G7.EffectiveWordCoefficients.wordRows_actual','GProgram.G7.EffectiveWordCoefficients.polynomial_naturalWordRows','GProgram.G7.EffectiveWordCoefficients.naturalWordRows_actual'])],
 ['Every literal original admitted entering Code and finite original-ID word','Same symbolic variable bank across all interval slots and original hybrids, including repeated slots','Exact per-step coefficient identities supplied by epoch uniqueness and concrete node/exit providers','Natural initialization enumerates the complete once-drawn original register, including empty Copy'],
 'Concrete stepRows and sparse coordinate renaming discharge the generic word theorem premise; natural literal bind preserves all destination fibres and the original register draw',
 ['Fresh prerequisite and root kernel/audit checks pending','Generated calendar/date/phase permutation and optional terminal-completion consumers remain separate','Universal native encoding/normalization and runtime dictionary/cap correspondence remain separate'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/WORD-PROVIDER-READBACK-20261010.md')], ['G7-SINGLE-EPOCH-TABLE-IDENTITY','G7-CONCRETE-ORIGINAL-NODE-COEFFICIENTS','G7-SPARSE-WORD-COMPOSITION','G7-EXECUTABLE-INITIALIZATION-COEFFICIENTS','G7-COMPLETED-LAW'])
add('G7-ORIGINAL-WORD-NATIVE-FIXTURES','G7/G6/Rust','Nine typed original full-word coefficient controls from unchanged private input origins','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalWordFixture.lean',['UnifiedLean.G7.OriginalWordFixture.registry2','UnifiedLean.G7.OriginalWordFixture.rootState_sourceValid','UnifiedLean.G7.OriginalWordFixture.fixtureNamed']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalWordFixtureMain.lean',['main'])],
 ['Previously admitted two-tip and parallel-occurrence sources, literal encodeActual conditional input images','Same frozen sample/label map, original register, current-owner routing and registry-ID gamma convention','Full ordered selected-view fibres, exact whole exponent vectors and rational coefficients; repeated slots reuse coordinates','Seven frozen finite word controls plus the two separately frozen parallel finite hybrid controls; no terminal completion'],
 'Instantiates the concrete actual sparse word and once-drawn natural providers on exact original typed sources, preserving every coefficient and one literal destination witness per selected fibre',
 ['Fresh prerequisite/root kernel checking, complete owned audits and actual nine-context evaluator comparison pending','The omitted ordinaryThreeFinite needs a separately admitted three-taxon original source','General encoding/normalization/dictionary/resource-cap and generated-calendar refinement remain separate'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/design/evidence/word-fixture-freeze-1/INVENTORY.json'),document_ref(base+'2026-10-10-codex-lean-rust-parity/design/evidence/word-hybrid-fixture-freeze-1/INVENTORY.json'),document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/WORD-PROVIDER-READBACK-20261010.md')], ['G7-CONCRETE-ORIGINAL-WORD-COEFFICIENTS','G7-ORIGINAL-BOUNDARY-NATIVE-FIXTURES'])
add('G7-CONCRETE-ORIGINAL-COMPLETED-WORD-COEFFICIENTS','G7/G6/Rust','Finite literal full-root word endpoints compose to unchanged completedPolynomial at every coefficient','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7EffectiveCompletedWordCoefficients.lean',['GProgram.G7.EffectiveCompletedWordCoefficients.polynomial_completedRows','GProgram.G7.EffectiveCompletedWordCoefficients.polynomial_completedWordRows','GProgram.G7.EffectiveCompletedWordCoefficients.polynomial_completedNaturalWordRows']),
 (base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7CompletedCalendarPolynomial.lean',['GProgram.G7.CompletedCalendarPolynomial.completedPolynomial','GProgram.G7.CompletedCalendarPolynomial.actual_natural_completed_calendar_polynomial'])],
 ['Nonempty Copy and one positive original pair-rate bank','Every literal raw finite endpoint, including zero-coefficient branches, has actual all-copy AncestralRoot support','Complete selected genealogy/location/full-register fibre and same original symbolic bank'],
 'Reuses accepted genuine rational ancestral-completion identity before literal bind/product partition; conditional and natural word endpoints target the unchanged entire completedPolynomial',
 ['Fresh prerequisites and kernel/audit checking pending','Derivation of raw sparse-row ancestral support for every generated calendar remains separate','General native dictionary/normalization and terminal-wrapper refinement remain separate'],
 [document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/WORD-PROVIDER-READBACK-20261010.md'),document_ref(base+'2026-10-10-codex-lean-rust-parity/design/WORD-COMPLETION-EXTENSION-20261010T1300Z.md')], ['G7-CONCRETE-ORIGINAL-WORD-COEFFICIENTS','G7-SUPPORT-ANCESTRAL-COMPLETION','G7-COMPLETED-LAW'])
add('G7-ORIGINAL-BOUNDARY-NATIVE-FIXTURES','G7/G6/Rust','Twelve exact conditional original boundary tables with complete selected views and literal witnesses','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalBoundaryFixture.lean',['UnifiedLean.G7.OriginalBoundaryFixture.siteState_sourceValid','UnifiedLean.G7.OriginalBoundaryFixture.carriedState_sourceValid','UnifiedLean.G7.OriginalBoundaryFixture.ordinary_degree','UnifiedLean.G7.OriginalBoundaryFixture.fixtureNamed']),
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G7OriginalBoundaryFixtureMain.lean',['main'])],
 ['Actual encodeActual entering image on the two-tip and separately admitted original parallel source','Original gamma=true/parent1; COMMON conditions on the unchanged entering register','Current live-owner fibres, empty copies, carried and outside trees, permuted injective labels and original E2/E3 occurrence IDs','Ordinary entry has the actual incoming degree-one proof; root entry keeps the actual original root'],
 'Saved actual-source fixture definitions and serializer match the twelve frozen design contexts; the actual inherited sparse boundary readout is used instead of an approximate independent recurrence',
 ['Fresh boundary proof, source/audit and actual evaluator checks pending','Twelve independent Lean/Rust/whole-copy marginalization comparisons pending','Generic normalization/serializer correctness and universal Rust refinement remain open'],
 [base+'2026-10-10-codex-lean-rust-parity/design/BOUNDARY-REFINEMENT.md',base+'2026-10-10-codex-lean-rust-parity/reuse/CONTINUATION-20261010.md'], ['G7-EXECUTABLE-BOUNDARY-COEFFICIENTS','G7-ORIGINAL-EPOCH-NATIVE-FIXTURES'])
add('G6-ORIGINAL-POPULATION-EXPOSURE','G6/G7','Same original retained-state epoch law at equal positive population exposure','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6OriginalPopulationExposure.lean',['GProgram.G6.OriginalPopulationExposure.original_epoch_eq_of_survival_eq','GProgram.G6.OriginalPopulationExposure.original_epoch_eq_of_exposure_eq','GProgram.G6.OriginalPopulationExposure.original_epoch_reader_eq_of_exposure_eq','GProgram.G6.OriginalPopulationExposure.original_epoch_entering_mixture_eq_of_exposure_eq'])],
 ['Same actual original source, entering Code and original population','All Copy co-located in that population; positive original rate banks and nonnegative durations','Arbitrary same-Code reader and arbitrary correlated entering prior supported on co-located codes'],
 'Direct reuse of unchanged actual_population_polynomial transports the entire retained PMF at equal exposure, including all genealogy, location and original register fields',
 ['Different population/graph forest-key transport remains separate','No positive compressed-chain reconstruction, chronological internal-merger retiming or global G6 closure follows'],
 [base+'2026-10-10-codex-lean-rust-parity/lean/ORIGINAL-POPULATION-CERTIFICATE.json',base+'2026-10-10-codex-lean-rust-parity/quality/PROOF-EXTENSION-REVIEW.json'], ['G7-EPOCH','G1-ORIGINAL'])
add('G6-ORIGINAL-POPULATION-SPECTRAL-SUPPORT','G6/G7','Every nonzero original population coefficient has a Kingman lineage-count death-level exponent','new_draft_compilation_pending',[
 (base+'2026-10-10-codex-lean-rust-parity/reuse/sources/G6OriginalPopulationSpectralSupport.lean',['GProgram.G6.OriginalPopulationSpectralSupport.original_kernelExpr_level_support','GProgram.G6.OriginalPopulationSpectralSupport.original_populationPolynomial_coeff_zero_of_non_level','GProgram.G6.OriginalPopulationSpectralSupport.original_populationPolynomial_nonzero_coeff_level'])],
 ['Any actual admitted entering/destination Code and arbitrary finite original Copy','Unchanged kernelExpr recurrence, arbitrary fuel and exact rational polynomial'],
 'Every surviving monomial lies at choose(j,2) with j no larger than the entering live count; this reuses the actual original merger-cardinality theorem',
 ['Coefficient norm bounds, count-conditioned forest weights, Caratheodory compression and positive reconstruction remain separate','No full G6 master certificate follows'],
 [base+'2026-10-10-codex-lean-rust-parity/lean/ORIGINAL-POPULATION-CERTIFICATE.json',base+'2026-10-10-codex-lean-rust-parity/quality/PROOF-EXTENSION-REVIEW.json'], ['G7-EPOCH','G6-ORIGINAL-POPULATION-EXPOSURE'])
add('G7-COMPLETED-LAW','G7/G6','Natural/controlled original completed-calendar polynomial response chain','inherited_scoped_formal_complete',[
 (base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7CompletedCalendarPolynomial.lean',['GProgram.G7.CompletedCalendarPolynomial.actual_natural_completed_calendar_polynomial','GProgram.G7.CompletedCalendarPolynomial.actual_controlled_completed_calendar_polynomial'])],
 ['One finite original graph and parent registry','One original natural register draw and source-specific COMMON/current-owner INDEPENDENT routing','Shared actual segment-survival/gamma coordinates; fixed original-ID masks','Nonempty finite copy carrier for infinite completion interpretation'],
 'Original boundaries, natural initialization, physical epochs and same-source ancestral completion compose into a proved completed response law',
 ['Whole-edge/source-open-cube parameter ties are not independent by declaration','Executable coefficient extraction, cofacial admission and policy/rank/resource selection are not supplied'],
 [base+'2026-10-09-dot-g7-completed-calendar-polynomial-2330z/README.md'], ['G7-EPOCH','G2 original-register/projectivity carriers'])
add('G7-POLICY-MASTER','G7','Effective finite-registry legal Pareto/policy or admitted response-consistent lower-certificate endpoint','formalization_open',[],
 ['Complete finite original registry','Original finite unranked readout menu and shared source bank','Exact-law reset/deletion-closed trajectory resource contract','Semialgebraic real action/sign/algebraic-selection model'],
 'Accepted hand characterization and source/compiler components remain the governing mathematics',
 ['Exact original cofacial admission and independent whole-edge source-family coverage','Executable coefficient composition from checked sparse epoch through boundaries/once-drawn initialization/completed calendars','Complete same-source Winning syntax and effective real QE, with action/lower-witness selection relative to the actual history field','Exact Pareto/policy/certificate producer; semantic rank/deletion consumers are existing candidates requiring repair/composition rather than absent proofs'],
 [base+'2026-10-10-dot-g7-qe-interface-review-0026z/README.md',base+'2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md',document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/G7-CLOSURE-AUDIT-20261010.md'),document_ref(base+'2026-10-10-codex-lean-rust-parity/reuse/G7-CLOSURE-DISCOVERY-20261010.json')], ['G7-CENSUS','G7-COMPLETED-LAW','G7-ORIGINAL-FAMILY-CARRIER-COMPOSITION','G1 causal unranked context','G2 sample deletion'])
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
# The separately isolated recovered graph preserves the original failed source
# and admits this exact repaired derivative with a complete owned audit.
accepted_recovery=HERE.parent/'lean/evidence/recovery/coefficients/20261010T111018.094654Z/run-20261010T111032.651895Z'
if accepted_recovery.exists():
    final=json.loads((accepted_recovery/'FINAL-RECEIPT.json').read_text())
    component=json.loads((accepted_recovery/'attempts/00001-G7EffectiveFullEpochCoefficients/receipt.json').read_text())
    audit=json.loads((accepted_recovery/'attempts/00003-OwnedAudit/work/AUDIT-RESULT.json').read_text())
    derivative=next(r for r in records if r['id']=='G7-FULL-EPOCH-COEFFICIENTS')
    current=next(p for p in derivative['providers'] if '/reuse/sources/' in p['path'])
    if (final['status']=='PASS_ALL_REQUESTED_TARGETS' and final['kernel_checking']
        and final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable']
        and component['exit_code']==0 and component['source_and_imports_stable']
        and component['source_sha256']==current['sha256']
        and not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and not audit['missing_modules']):
        derivative['status']='new_kernel_checked_exact_source'
        derivative['evidence'].append(str((accepted_recovery/'FINAL-RECEIPT.json').relative_to(ROOT)))
        derivative['evidence'].append(str((accepted_recovery/'attempts/00003-OwnedAudit/work/AUDIT-RESULT.json').relative_to(ROOT)))
        derivative['genuinely_remaining']=['Separate actual native coefficient codegen/runtime extraction receipt','Efficient restricted coefficient table/dictionary correspondence','Native unordered LAW quotient and universal Rust refinement; full G3/G4 remain open']
# The support/encoding proofs and original native fixture share a complete
# isolated audit. Only each exact freshly compiled source is promoted here;
# the successful aggregate does not establish native execution or Rust parity.
accepted_population=HERE.parent/'lean/evidence/source-population/20261010T112848.298732Z/run-20261010T112858.338259Z'
if accepted_population.exists():
    final=json.loads((accepted_population/'FINAL-RECEIPT.json').read_text())
    target=json.loads((accepted_population/'targets/extraction_original-population-fixture/RESULT.json').read_text())
    audit_path=accepted_population/'attempts/00016-OwnedAudit/work/AUDIT-RESULT.json'
    audit=json.loads(audit_path.read_text())
    selected=set(audit['selected_modules'])
    if (final['status']=='PASS_ALL_REQUESTED_TARGETS' and final['kernel_checking']
        and final['trust_level']==0 and final['compiler_identity_stable']
        and final['native_runtime_final_rehash_stable'] and target['status']=='PASS'
        and len(selected)==target['closure_modules']
        and not audit['owned_axioms'] and not audit['nonstandard_axiom_rows']
        and not audit['missing_modules']):
        for key,attempt,gaps in [
            ('G7-EXECUTABLE-COEFFICIENT-SUPPORT','00001-G7EffectiveCoefficientSupport',[
                'Complete normalized coefficient table/dictionary correspondence remains separate',
                'Ordered-to-unordered quotient aggregation and universal Rust refinement remain separate']),
            ('G7-ENCODED-MERGER-SUPPORT','00002-G7EncodedMergerSupport',[
                'Full normalized dictionary/serialization equality, quotient linearity and universal Rust refinement remain separate']),
            ('G7-ORIGINAL-POPULATION-NATIVE-FIXTURES','00014-G7OriginalPopulationFixture',[
                'Separate native code generation and eight-fixture independent Lean/Rust/oracle execution remain pending',
                'Finite canonical serializer checks do not establish a universal Code-to-LAW quotient theorem'])]:
            record=next(r for r in records if r['id']==key)
            current=next(p for p in record['providers'] if '/reuse/sources/' in p['path'])
            component_path=accepted_population/'attempts'/attempt/'receipt.json'
            component=json.loads(component_path.read_text())
            if (component['status']=='PASS_FRESH_KERNEL_CHECK' and component['exit_code']==0
                and component['source_and_imports_stable']
                and component['module'] in selected
                and component['source_sha256']==current['sha256']):
                record['status']='new_kernel_checked_exact_source'
                record['evidence'].extend(str(p.relative_to(ROOT)) for p in [
                    accepted_population/'FINAL-RECEIPT.json',component_path,audit_path])
                record['genuinely_remaining']=gaps
                record['fresh_audit_context']={
                    'modules':target['closure_modules'],
                    'declarations':audit['declaration_count'],
                    'theorems':audit['theorem_declaration_count'],
                    'fresh_components':final['counts']['fresh_components'],
                    'exact_context_reuses':final['counts']['cache_reuse'],
                    'native_execution_claimed':False}
# Actual imported-definition evaluation and independent finite comparison are
# separate from the kernel audit. Lean's execution mode is preserved exactly.
execution_path=HERE.parent/'lean/evidence/source-population-execution/20261010T113514.964547Z/RECEIPT.json'
comparison_path=HERE.parent/'design/evidence/population-lean-rust-review-1/RECEIPT.json'
accepted_join=HERE.parent/'lean/evidence/proof-extensions/extraction_g7-support-and-join/20261010T115655.883875Z/run-20261010T115841.067259Z'
if (accepted_join/'FINAL-RECEIPT.json').exists():
    final=json.loads((accepted_join/'FINAL-RECEIPT.json').read_text())
    assert final['status']=='PASS_ALL_REQUESTED_TARGETS'
    assert final['kernel_checking'] and final['trust_level']==0
    assert final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable']
    for key,module,attempt,audit_attempt,gaps in [
        ('G7-CONSTRUCTIVE-PANEL-JOIN','G7ConstructivePanelJoin','00001','00003',[
            'Same entering register and valid population factorization remain inherited epoch-law premises',
            'Whole executable epoch extraction and universal Rust refinement remain separate']),
        ('G7-SUPPORT-SELECTED-EXTRACTION','G7PopulationSelectedSupport','00004','00006',[
            'General sparse normalization/serializer and universal Rust refinement remain separate',
            'Full epoch row-product consumer and compiled mixed fixtures remain separate']),
        ('G7-EFFECTIVE-PANEL-JOIN','G7EffectivePanelJoin','00007','00009',[
            'Whole epoch support products, normalized dictionary and universal Rust refinement remain separate'])]:
        record=next(r for r in records if r['id']==key)
        own=next(p for p in record['providers'] if '/reuse/sources/' in p['path'])
        component_path=accepted_join/'attempts'/f'{attempt}-{module}'/'receipt.json'
        component=json.loads(component_path.read_text())
        audit_path=accepted_join/'attempts'/f'{audit_attempt}-OwnedAudit/work/AUDIT-RESULT.json'
        if audit_path.exists():
            audit=json.loads(audit_path.read_text())
        else:
            audit_path=Path(str(audit_path)+'.gz')
            audit=json.loads(gzip.decompress(audit_path.read_bytes()))
        target_path=accepted_join/'targets'/f'extraction_g7-support-and-join_{module}'/'RESULT.json'
        target=json.loads(target_path.read_text())
        if (component['status']=='PASS_FRESH_KERNEL_CHECK' and component['exit_code']==0
            and component['source_and_imports_stable'] and component['source_sha256']==own['sha256']
            and target['status']=='PASS' and len(audit['selected_modules'])==target['closure_modules']
            and module in audit['selected_modules'] and not audit['owned_axioms']
            and not audit['nonstandard_axiom_rows'] and not audit['missing_modules']):
            record['status']='new_kernel_checked_exact_source'
            record['genuinely_remaining']=gaps
            record['evidence'].extend(str(p.relative_to(ROOT)) for p in [
                accepted_join/'FINAL-RECEIPT.json',component_path,target_path,audit_path])
            record['fresh_audit_context']={'modules':target['closure_modules'],
                'declarations':audit['declaration_count'],'theorems':audit['theorem_declaration_count'],
                'native_execution_claimed':False,'scope':'Separate exact target; context counts overlap'}
# A passing separately audited target may be preserved in a run that also
# contains an unrelated failed target. Promote only the named PASS target;
# the run's overall failure remains part of the evidence, never a whole-run pass.
for key,module,stamp,run,gaps in [
    ('G7-SPARSE-ROW-PRODUCTS','G7SparseRowProducts','20261010T122448.514985Z','20261010T122456.335105Z',[
        'General normalized dictionary/serializer correctness and universal Rust refinement remain open']),
    ('G7-FULL-EPOCH-SUPPORT','G7FullEpochSupport','20261010T122657.858633Z','20261010T122706.573931Z',[
        'Eight ordinary and separately typed parallel mixed epoch compiled evaluator comparisons pending',
        'General normalized dictionary/serializer correctness and universal Rust refinement remain open',
        'Sparse original boundary/initialization/calendar/completion composition remains separate'])]:
    accepted=HERE.parent/'lean/evidence/proof-extensions/extraction_g7-full-epoch-support'/stamp/('run-'+run)
    if not accepted.exists():
        continue
    final_path=accepted/'FINAL-RECEIPT.json'
    component_path=accepted/'attempts'/f'00001-{module}'/'receipt.json'
    target_path=accepted/'targets'/f'extraction_g7-full-epoch-support_{module}'/'RESULT.json'
    audit_path=accepted/'attempts/00003-OwnedAudit/work/AUDIT-RESULT.json'
    if not audit_path.exists():
        audit_path=Path(str(audit_path)+'.gz')
    raw=audit_path.read_bytes()
    audit=json.loads(gzip.decompress(raw) if audit_path.suffix=='.gz' else raw)
    final=json.loads(final_path.read_text())
    component=json.loads(component_path.read_text())
    target=json.loads(target_path.read_text())
    record=next(r for r in records if r['id']==key)
    own=next(p for p in record['providers'] if '/reuse/sources/' in p['path'])
    if (final['status'] in ['PASS_ALL_REQUESTED_TARGETS','INCOMPLETE_TARGET_FAILURES_PRESERVED']
        and final['kernel_checking'] and final['trust_level']==0
        and final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable']
        and target['status']=='PASS' and len(audit['selected_modules'])==target['closure_modules']
        and module in audit['selected_modules'] and not audit['owned_axioms']
        and not audit['nonstandard_axiom_rows'] and not audit['missing_modules']
        and component['status']=='PASS_FRESH_KERNEL_CHECK' and component['exit_code']==0
        and component['source_and_imports_stable'] and component['source_sha256']==own['sha256']):
        record['status']='new_kernel_checked_exact_source'
        record['genuinely_remaining']=gaps
        record['evidence'].extend(str(p.relative_to(ROOT)) for p in [
            final_path,component_path,target_path,audit_path])
        record['fresh_audit_context']={'modules':target['closure_modules'],
            'declarations':audit['declaration_count'],'theorems':audit['theorem_declaration_count'],
            'native_execution_claimed':False,
            'scope':'Only this passing complete exact target; separate target counts overlap',
            'overall_run_status':final['status']}
# Later separate complete certificates can cover only a subset of one fixture
# obligation. Keep that partial status rather than promoting uncompiled peers.
for certificate_name,keys in [
    ('ORIGINAL-POPULATION-CERTIFICATE.json',{
        'G6-ORIGINAL-POPULATION-EXPOSURE':'G6OriginalPopulationExposure',
        'G6-ORIGINAL-POPULATION-SPECTRAL-SUPPORT':'G6OriginalPopulationSpectralSupport'}),
    ('ORIGINAL-EPOCH-FIXTURE-CERTIFICATE.json',{
        'G7-ORIGINAL-EPOCH-NATIVE-FIXTURES':None}),
    ('ORIGINAL-PARALLEL-EPOCH-FIXTURE-CERTIFICATE.json',{
        'G7-ORIGINAL-EPOCH-NATIVE-FIXTURES':None}),
    ('EFFECTIVE-BOUNDARY-CERTIFICATE.json',{
        'G7-EXECUTABLE-BOUNDARY-COEFFICIENTS':'G7EffectiveBoundaryCoefficients'}),
    ('ORIGINAL-BOUNDARY-FIXTURE-CERTIFICATE.json',{
        'G7-ORIGINAL-BOUNDARY-NATIVE-FIXTURES':None}),
    ('EFFECTIVE-COMPLETION-CERTIFICATE.json',{
        'G7-SUPPORT-ANCESTRAL-COMPLETION':'G7EffectiveAncestralCompletion'}),
    ('ORIGINAL-COMPLETION-FIXTURE-CERTIFICATE.json',{
        'G7-ORIGINAL-COMPLETION-NATIVE-FIXTURES':None}),
    ('EFFECTIVE-INITIALIZATION-CERTIFICATE.json',{
        'G7-EXECUTABLE-INITIALIZATION-COEFFICIENTS':'G7EffectiveInitializationCoefficients'}),
    ('SELECTED-EPOCH-UNIQUENESS-CERTIFICATE.json',{
        'G7-SINGLE-EPOCH-TABLE-IDENTITY':'G7SelectedEpochTableUniqueness'}),
    ('SPARSE-WORD-COMPOSITION-CERTIFICATE.json',{
        'G7-SPARSE-WORD-COMPOSITION':'G7SparseWordComposition'}),
    ('EFFECTIVE-NODE-CERTIFICATE.json',{
        'G7-CONCRETE-ORIGINAL-NODE-COEFFICIENTS':'G7EffectiveNodeCoefficients'}),
    ('EFFECTIVE-WORD-CERTIFICATE.json',{
        'G7-CONCRETE-ORIGINAL-WORD-COEFFICIENTS':'G7EffectiveWordCoefficients'}),
    ('ORIGINAL-WORD-FIXTURE-CERTIFICATE.json',{
        'G7-ORIGINAL-WORD-NATIVE-FIXTURES':None}),
    ('EFFECTIVE-COMPLETED-WORD-CERTIFICATE.json',{
        'G7-CONCRETE-ORIGINAL-COMPLETED-WORD-COEFFICIENTS':'G7EffectiveCompletedWordCoefficients'})]:
    certificate_path=HERE.parent/'lean'/certificate_name
    if not certificate_path.exists():
        continue
    certificate=json.loads(certificate_path.read_text())
    if certificate['status']!='PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS':
        continue
    accepted=HERE.parent/'lean'/certificate['evidence']
    final_path=accepted/'FINAL-RECEIPT.json'
    final=json.loads(final_path.read_text())
    if not (final['status']=='PASS_ALL_REQUESTED_TARGETS' and final['kernel_checking']
        and final['trust_level']==0 and final['compiler_identity_stable']
        and final['native_runtime_final_rehash_stable']):
        continue
    for key,required_module in keys.items():
        record=next(r for r in records if r['id']==key)
        owned=[p for p in record['providers'] if '/reuse/sources/' in p['path']]
        validated=[]
        for own in owned:
            module=Path(own['path']).stem
            if required_module and module!=required_module:
                continue
            matches=[(name,t) for name,t in certificate['targets'].items() if t['roots']==[module]]
            if len(matches)!=1:
                continue
            target_name,target=matches[0]
            component_paths=list(accepted.glob(f'attempts/*-{module}/receipt.json'))
            if len(component_paths)!=1:
                continue
            component_path=component_paths[0]
            component=json.loads(component_path.read_text())
            audit_path=accepted/target['audit_distribution']
            raw=audit_path.read_bytes()
            if audit_path.suffix=='.gz':
                raw=gzip.decompress(raw)
            audit=json.loads(raw)
            if (target['status']=='PASS_FRESH_AGGREGATE_AND_COMPLETE_OWNED_AUDIT'
                and component['status']=='PASS_FRESH_KERNEL_CHECK' and component['exit_code']==0
                and component['source_sha256']==own['sha256'] and component['source_and_imports_stable']
                and hashlib.sha256(raw).hexdigest()==target['audit_raw_sha256']
                and module in audit['selected_modules']
                and len(audit['selected_modules'])==target['closure_modules']
                and audit['declaration_count']==target['owned_declarations']
                and audit['theorem_declaration_count']==target['owned_theorems']
                and not audit['owned_axioms'] and not audit['nonstandard_axiom_rows']
                and not audit['missing_modules']):
                validated.append({'module':module,'source_sha256':own['sha256'],
                    'modules':target['closure_modules'],'declarations':audit['declaration_count'],
                    'theorems':audit['theorem_declaration_count'],'native_execution_claimed':False,
                    'component_receipt':str(component_path.relative_to(ROOT)),
                    'owned_audit':str(audit_path.relative_to(ROOT))})
                record['evidence'].extend(str(p.relative_to(ROOT)) for p in [certificate_path,final_path,component_path,audit_path])
        if validated:
            prior={v['module']:v for v in record.get('fresh_source_validation',[])}
            prior.update({v['module']:v for v in validated})
            record['fresh_source_validation']=list(prior.values())
            record['status']=('new_kernel_checked_exact_source' if len(prior)==len(owned)
                else 'partially_kernel_checked_exact_sources_execution_pending')
            if key=='G7-ORIGINAL-EPOCH-NATIVE-FIXTURES':
                record['genuinely_remaining']=[
                    'Eight ordinary compiled-evaluator comparisons and separately typed parallel ninth remain pending',
                    'General normalized dictionary/serializer correctness and universal Rust refinement remain open']
            elif key=='G7-EXECUTABLE-BOUNDARY-COEFFICIENTS':
                record['genuinely_remaining']=[
                    'Twelve typed original boundary evaluator comparisons remain pending',
                    'General normalization/serialization and universal Rust refinement remain open',
                    'Finite word/calendar legal-order and once-drawn initialization/completion composition remain separate']
            elif key=='G7-SUPPORT-ANCESTRAL-COMPLETION':
                record['genuinely_remaining']=[
                    'Six direct typed original compiled-evaluator completion comparisons remain pending',
                    'Concrete full word completion/encoding/normalization refinement remains separate',
                    'Chosen epoch-table coefficient identity is a separate pending composition']
            elif key=='G7-EXECUTABLE-INITIALIZATION-COEFFICIENTS':
                record['genuinely_remaining']=[
                    'Concrete natural word/calendar composition and actual typed evaluator comparisons remain separate',
                    'General normalization/serializer correctness and universal Rust refinement remain open']
            elif key=='G7-SINGLE-EPOCH-TABLE-IDENTITY':
                record['genuinely_remaining']=[
                    'Concrete node/exit table and word/natural/completed consumers remain separate compositions',
                    'General native encoding/normalization refinement remains separate; shared multi-slot calendar evaluations do not form an independent cube']
            elif key=='G7-SPARSE-WORD-COMPOSITION':
                record['genuinely_remaining']=[
                    'Exact per-step selected polynomial identity remains an explicit premise of this generic theorem',
                    'Concrete original node/slot/natural word and calendar consumer remain separate compositions',
                    'General normalized dictionary/serializer correctness, resource-cap semantics and universal Rust refinement remain open']
            elif key=='G7-CONCRETE-ORIGINAL-NODE-COEFFICIENTS':
                record['genuinely_remaining']=[
                    'Concrete word/natural/calendar composition and actual evaluator controls remain separate',
                    'Universal native input encoding/normalization and dictionary refinement remain separate']
            elif key=='G7-CONCRETE-ORIGINAL-WORD-COEFFICIENTS':
                record['genuinely_remaining']=[
                    'Generated calendar/date/phase enumeration and terminal completion consumers remain separate',
                    'Universal native encoding/normalization and runtime dictionary/cap correspondence remain separate']
            elif key=='G7-ORIGINAL-WORD-NATIVE-FIXTURES':
                record['genuinely_remaining']=[
                    'Nine original-word evaluator comparisons remain separately pending',
                    'The omitted ordinaryThreeFinite requires a separately admitted three-taxon original source',
                    'General native encoding/normalization/dictionary/resource-cap and generated-calendar refinement remain separate']
            elif key=='G7-CONCRETE-ORIGINAL-COMPLETED-WORD-COEFFICIENTS':
                record['genuinely_remaining']=[
                    'Derivation of raw sparse-row ancestral support for every generated calendar remains separate',
                    'General native dictionary/normalization and terminal-wrapper refinement remain separate']
# Rank and carrier roots share one complete five-root semantic target. Exact
# cached kernel admissions remain distinguished from the fresh carrier check.
semantic_path=HERE.parent/'lean/SEMANTIC-RANK-RECOVERY-CERTIFICATE.json'
if semantic_path.exists():
    certificate=json.loads(semantic_path.read_text())
    accepted=HERE.parent/'lean'/certificate['evidence']
    final_path=accepted/'FINAL-RECEIPT.json'
    final=json.loads(final_path.read_text())
    target=certificate['targets']['recovery/g7-semantic-rank']
    audit_path=accepted/target['audit_distribution']
    raw=gzip.decompress(audit_path.read_bytes())
    audit=json.loads(raw)
    roots={'G7ExactLawResourceGame','G7ActualExactLawResponses','G7ExactLawRankCompression',
        'G7OriginalFamilyStrategy','G7OriginalCarrierCoverage'}
    if (certificate['status']=='PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS'
        and final['status']=='PASS_ALL_REQUESTED_TARGETS' and final['kernel_checking']
        and final['trust_level']==0 and final['compiler_identity_stable']
        and final['native_runtime_final_rehash_stable']
        and set(target['roots'])==roots and roots.issubset(audit['selected_modules'])
        and hashlib.sha256(raw).hexdigest()==target['audit_raw_sha256']
        and len(audit['selected_modules'])==target['closure_modules']
        and audit['declaration_count']==target['owned_declarations']
        and audit['theorem_declaration_count']==target['owned_theorems']
        and not audit['owned_axioms'] and not audit['nonstandard_axiom_rows']
        and not audit['missing_modules']):
        rank=next(r for r in records if r['id']=='G7-RANK-COMPRESSION-REPAIR')
        family=next(r for r in records if r['id']=='G7-ORIGINAL-FAMILY-CARRIER-COMPOSITION')
        rank_provider=rank['providers'][0]
        family_provider=family['providers'][0]
        carrier_provider=next(p for p in family['providers'] if '/reuse/sources/' in p['path'])
        pins=certificate['source_pins']
        if (pins['G7ExactLawRankCompression']==rank_provider['sha256']
            and pins['G7OriginalFamilyStrategy']==family_provider['sha256']
            and pins['G7OriginalCarrierCoverage']==carrier_provider['sha256']):
            for record in [rank,family]:
                record['status']='new_kernel_checked_exact_compatible_composition'
                record['evidence'].extend(str(p.relative_to(ROOT)) for p in
                    [semantic_path,final_path,audit_path])
                record['fresh_audit_context']={'modules':target['closure_modules'],
                    'declarations':audit['declaration_count'],
                    'theorems':audit['theorem_declaration_count'],
                    'kernel_admission':'Exact original-context caches plus fresh carrier; complete new aggregate/audit',
                    'native_execution_claimed':False,
                    'older_failed_source_bytes_promoted':False}
            rank['genuinely_remaining']=[
                'Effective simulation/span testing, complete real QE/action selection and G7 Pareto extraction remain separate']
            family['validated_composition_sources']=[
                {'module':'G7OriginalFamilyStrategy','source_sha256':family_provider['sha256']},
                {'module':'G7OriginalCarrierCoverage','source_sha256':carrier_provider['sha256']},
                {'module':'G7ExactLawRankCompression','source_sha256':rank_provider['sha256']}]
            family['genuinely_remaining']=[
                'Effective syntax, cofacial admission, whole-edge coverage and real QE/selection/Pareto producer remain separate']
            policy=next(r for r in records if r['id']=='G7-POLICY-MASTER')
            policy['accepted_semantic_dependency']={
                'certificate':str(semantic_path.relative_to(ROOT)),
                'modules':target['closure_modules'],
                'declarations':audit['declaration_count'],
                'theorems':audit['theorem_declaration_count'],
                'roots':sorted(roots),
                'effective_policy_engine_claimed':False}
            policy['genuinely_remaining']=[
                'Exact original cofacial admission and independent whole-edge source-family coverage',
                'Executable coefficient composition from checked sparse epoch through boundaries/once-drawn initialization/completed calendars',
                'Complete same-source Winning syntax and effective real QE, with action/lower-witness selection relative to the actual history field',
                'Exact Pareto/policy/certificate producer; the accepted semantic rank/deletion/family/carrier composition is a dependency, not an effective producer']
# The ordinary eight and parallel ninth retain separate complete source contexts
# and separate evaluator receipts. Neither certificate alone promotes all nine.
epoch_fixture=next(r for r in records if r['id']=='G7-ORIGINAL-EPOCH-NATIVE-FIXTURES')
if epoch_fixture['status']=='new_kernel_checked_exact_source':
    groups=[('ORIGINAL-EPOCH-NATIVE-EXECUTION-RESULT.json',
        'epoch-lean-rust-review-2',
        {'empty','oneAncestral','twoEdgePanels','edgeAncestral','nodeIdentity',
         'carriedNodeExterior','permutedRestricted','frozenRegister'},
        {'G7OriginalEpochFixture','G7OriginalEpochFixtureMain'}),
        ('ORIGINAL-PARALLEL-EPOCH-NATIVE-EXECUTION-RESULT.json',
        'epoch-lean-rust-parallel-review-1',{'parallelPanels'},
        {'G7OriginalParallelEpochFixture','G7OriginalParallelEpochFixtureMain'})]
    accepted_groups=[]
    for execution_name,comparison_name,expected,modules in groups:
        execution_path_epoch=HERE.parent/'lean'/execution_name
        comparison_path_epoch=HERE.parent/'design/evidence'/comparison_name/'RECEIPT.json'
        if not execution_path_epoch.exists() or not comparison_path_epoch.exists():
            continue
        execution=json.loads(execution_path_epoch.read_text())
        comparison=json.loads(comparison_path_epoch.read_text())
        cases={c['fixture']:c for c in comparison['cases']}
        own={Path(p['path']).stem:p['sha256'] for p in epoch_fixture['providers']}
        if (execution['status']=='PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL'
            and execution['exit_code']==0
            and execution['all_actual_imported_artifacts_compiler_and_native_libraries_final_stable']
            and execution['fixtures_total']==len(expected)
            and execution['fixtures_passed']==len(expected)
            and hashlib.sha256(comparison_path_epoch.read_bytes()).hexdigest()==execution['coefficient_review_receipt_sha256']
            and all(execution['source_pins'].get(module)==own[module] for module in modules)
            and comparison['pass'] and comparison['cases_passed']==len(expected)
            and comparison['cases_total']==len(expected) and set(cases)==expected
            and comparison['binary_pins_before']==comparison['binary_pins_after']
            and comparison['observed_input_pins_before']==comparison['observed_input_pins_after']
            and all(c['pass'] and not c['errors']
                and c['runs']['lean']['exit_code']==0 and c['runs']['rust']['exit_code']==0
                and not c['runs']['lean']['timed_out'] and not c['runs']['rust']['timed_out']
                for c in cases.values())):
            accepted_groups.append({'fixtures':sorted(expected),'cases_passed':len(expected),
                'cases_total':len(expected),'execution_mode':execution['execution_mode'],
                'standalone_elf_claimed':execution['standalone_elf_claimed'],
                'general_refinement_proof_claimed':False,
                'execution_receipt':str(execution_path_epoch.relative_to(ROOT)),
                'comparison_receipt':str(comparison_path_epoch.relative_to(ROOT))})
            epoch_fixture['evidence'].extend(str(p.relative_to(ROOT)) for p in
                [execution_path_epoch,comparison_path_epoch])
    epoch_fixture['finite_comparison_groups']=accepted_groups
    if len(accepted_groups)==len(groups):
        epoch_fixture['status']='new_kernel_checked_and_nine_finite_original_comparisons_pass'
        epoch_fixture['genuinely_remaining']=[
            'General normalization/serializer correctness and universal Rust refinement remain open',
            'Whole word/calendar input admission and composed coefficient identity remain separate']
        epoch_support=next(r for r in records if r['id']=='G7-FULL-EPOCH-SUPPORT')
        epoch_support['finite_consumer_comparisons']=accepted_groups
        epoch_support['genuinely_remaining']=[
            'General normalization/serializer correctness and universal Rust refinement remain open',
            'Concrete once-drawn initialization, word/calendar input admission and composed coefficient identity remain separate']
boundary_fixture=next(r for r in records if r['id']=='G7-ORIGINAL-BOUNDARY-NATIVE-FIXTURES')
boundary_execution_path=HERE.parent/'lean/ORIGINAL-BOUNDARY-NATIVE-EXECUTION-RESULT.json'
boundary_comparison_path=HERE.parent/'design/evidence/boundary-lean-rust-review-1/RECEIPT.json'
if (boundary_fixture['status']=='new_kernel_checked_exact_source'
    and boundary_execution_path.exists() and boundary_comparison_path.exists()):
    execution=json.loads(boundary_execution_path.read_text())
    comparison=json.loads(boundary_comparison_path.read_text())
    expected={'emptyCommon','emptyIndependent','commonFalse','commonTrue','independentTwo',
        'noOwnerAtSite','carriedOwnerOutside','permutedIndependent','registerRepeat',
        'ordinaryEntry','rootEntry','parallelExit'}
    cases={c['fixture']:c for c in comparison['cases']}
    own={Path(p['path']).stem:p['sha256'] for p in boundary_fixture['providers']}
    if (execution['status']=='PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL'
        and execution['exit_code']==0
        and execution['all_actual_imported_artifacts_compiler_and_native_libraries_final_stable']
        and execution['fixtures_total']==12 and execution['fixtures_passed']==12
        and hashlib.sha256(boundary_comparison_path.read_bytes()).hexdigest()==execution['coefficient_review_receipt_sha256']
        and all(execution['source_pins'].get(module)==source_hash for module,source_hash in own.items())
        and comparison['pass'] and comparison['cases_passed']==12 and comparison['cases_total']==12
        and set(cases)==expected
        and comparison['binary_pins_before']==comparison['binary_pins_after']
        and comparison['observed_input_pins_before']==comparison['observed_input_pins_after']
        and all(c['pass'] and not c['errors']
            and c['runs']['lean']['exit_code']==0 and c['runs']['rust']['exit_code']==0
            and not c['runs']['lean']['timed_out'] and not c['runs']['rust']['timed_out']
            for c in cases.values())):
        boundary_fixture['status']='new_kernel_checked_and_twelve_finite_original_comparisons_pass'
        boundary_fixture['evidence'].extend(str(p.relative_to(ROOT)) for p in
            [boundary_execution_path,boundary_comparison_path])
        boundary_fixture['finite_comparison']={'cases_passed':12,'cases_total':12,
            'execution_mode':execution['execution_mode'],
            'standalone_elf_claimed':execution['standalone_elf_claimed'],
            'oracle_algorithm':comparison['oracle_algorithm'],'general_refinement_proof_claimed':False}
        boundary_fixture['genuinely_remaining']=[
            'General normalization/serializer correctness and universal Rust refinement remain open',
            'Natural initialization/full word/completion composition remains separate']
        boundary=next(r for r in records if r['id']=='G7-EXECUTABLE-BOUNDARY-COEFFICIENTS')
        boundary['finite_consumer_comparison']=boundary_fixture['finite_comparison']
        boundary['genuinely_remaining']=[
            'General normalization/serialization and universal Rust refinement remain open',
            'Finite word/calendar legal-order and once-drawn initialization/completion composition remain separate']
completion_fixture=next(r for r in records if r['id']=='G7-ORIGINAL-COMPLETION-NATIVE-FIXTURES')
completion_execution_path=HERE.parent/'lean/ORIGINAL-COMPLETION-NATIVE-EXECUTION-RESULT.json'
completion_comparison_path=HERE.parent/'design/evidence/completion-compiled-oracle-actual-1/RECEIPT.json'
if (completion_fixture['status']=='new_kernel_checked_exact_source'
    and completion_execution_path.exists() and completion_comparison_path.exists()):
    execution=json.loads(completion_execution_path.read_text())
    comparison=json.loads(completion_comparison_path.read_text())
    expected={'completion1','completion2','completion3','completion4',
        'completionCarriedNonminimum','completionPermutedFour'}
    cases={c['fixture']:c for c in comparison['cases']}
    own={Path(p['path']).stem:p['sha256'] for p in completion_fixture['providers']}
    if (execution['status']=='PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL'
        and execution['exit_code']==0 and not execution['errors']
        and execution['all_actual_imported_artifacts_compiler_and_native_libraries_final_stable']
        and execution['fixtures_total']==6 and execution['fixtures_passed']==6
        and execution['full_view_rows_total']==257
        and hashlib.sha256(completion_comparison_path.read_bytes()).hexdigest()==execution['coefficient_review_receipt_sha256']
        and all(execution['source_pins'].get(module)==source_hash for module,source_hash in own.items())
        and comparison['pass'] and comparison['cases_passed']==6 and comparison['cases_total']==6
        and comparison['full_view_rows_total']==257 and set(cases)==expected
        and comparison['pins_before']==comparison['pins_after']
        and all(c['pass'] and not c['errors']
            and c['runs']['lean']['exit_code']==0 and c['runs']['rust']['exit_code']==0
            and not c['runs']['lean']['timed_out'] and not c['runs']['rust']['timed_out']
            for c in cases.values())):
        completion_fixture['status']='new_kernel_checked_and_six_finite_original_comparisons_pass'
        completion_fixture['evidence'].extend(str(p.relative_to(ROOT)) for p in
            [completion_execution_path,completion_comparison_path])
        completion_fixture['finite_comparison']={'cases_passed':6,'cases_total':6,
            'full_view_rows':257,'execution_mode':execution['execution_mode'],
            'standalone_elf_claimed':execution['standalone_elf_claimed'],
            'oracle_algorithm':comparison['oracle_algorithm'],'general_refinement_proof_claimed':False}
        completion_fixture['genuinely_remaining']=[
            'General native encoding/normalization refinement and full word wrapper/work correspondence remain separate']
        completion=next(r for r in records if r['id']=='G7-SUPPORT-ANCESTRAL-COMPLETION')
        completion['finite_consumer_comparison']=completion_fixture['finite_comparison']
        completion['genuinely_remaining']=[
            'Concrete full word completion/encoding/normalization refinement remains separate']
        chosen=next(r for r in records if r['id']=='G7-SINGLE-EPOCH-TABLE-IDENTITY')
        if chosen['status']!='new_kernel_checked_exact_source':
            completion['genuinely_remaining'].append(
                'Chosen epoch-table coefficient identity is a separate pending composition')
word_fixture=next(r for r in records if r['id']=='G7-ORIGINAL-WORD-NATIVE-FIXTURES')
word_execution_path=HERE.parent/'lean/ORIGINAL-WORD-NATIVE-EXECUTION-RESULT.json'
word_comparison_path=HERE.parent/'design/evidence/word-compiled-oracle-actual-1/RECEIPT.json'
if (word_fixture['status']=='new_kernel_checked_exact_source'
    and word_execution_path.exists() and word_comparison_path.exists()):
    execution=json.loads(word_execution_path.read_text())
    comparison=json.loads(word_comparison_path.read_text())
    expected={'emptyConditionalWord','emptyNaturalWord','emptyNaturalCommonWord',
        'conditionalCommonFalseWord','conditionalCommonTrueWord','repeatedIntervalSlot',
        'carriedOutsideWord','parallelCommonFinite','parallelIndependentFinite'}
    cases={c['fixture']:c for c in comparison['cases']}
    own={Path(p['path']).stem:p['sha256'] for p in word_fixture['providers']}
    if (execution['status']=='PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL'
        and execution['exit_code']==0 and not execution['errors']
        and execution['all_actual_imported_artifacts_compiler_and_native_libraries_final_stable']
        and execution['fixtures_total']==9 and execution['fixtures_passed']==9
        and execution['full_view_rows_total']==39
        and hashlib.sha256(word_comparison_path.read_bytes()).hexdigest()==execution['coefficient_review_receipt_sha256']
        and all(execution['source_pins'].get(module)==source_hash for module,source_hash in own.items())
        and comparison['pass'] and comparison['cases_passed']==9 and comparison['cases_total']==9
        and comparison['full_view_rows_total']==39 and set(cases)==expected
        and comparison['pins_before']==comparison['pins_after']
        and all(c['pass'] and not c['errors']
            and c['runs']['lean']['exit_code']==0 and c['runs']['rust']['exit_code']==0
            and not c['runs']['lean']['timed_out'] and not c['runs']['rust']['timed_out']
            for c in cases.values())):
        word_fixture['status']='new_kernel_checked_and_nine_finite_original_comparisons_pass'
        word_fixture['evidence'].extend(str(p.relative_to(ROOT)) for p in
            [word_execution_path,word_comparison_path])
        word_fixture['finite_comparison']={'cases_passed':9,'cases_total':9,
            'full_view_rows':39,'execution_mode':execution['execution_mode'],
            'standalone_elf_claimed':execution['standalone_elf_claimed'],
            'oracle_algorithm':comparison['oracle_algorithm'],'general_refinement_proof_claimed':False}
        word_fixture['genuinely_remaining']=[
            'The omitted ordinaryThreeFinite requires a separately admitted three-taxon original source',
            'General native encoding/normalization/dictionary/resource-cap and generated-calendar refinement remain separate']
        word=next(r for r in records if r['id']=='G7-CONCRETE-ORIGINAL-WORD-COEFFICIENTS')
        word['finite_consumer_comparison']=word_fixture['finite_comparison']
# The concrete checked word supplies every per-step identity while the generic
# theorem retains its explicit premise. Update only these compatible dependency
# gaps; generated-calendar enumeration and general Rust refinement stay open.
word=next(r for r in records if r['id']=='G7-CONCRETE-ORIGINAL-WORD-COEFFICIENTS')
if word['status']=='new_kernel_checked_exact_source':
    for key in ['G7-FULL-EPOCH-SUPPORT','G7-ORIGINAL-EPOCH-NATIVE-FIXTURES',
        'G7-EXECUTABLE-BOUNDARY-COEFFICIENTS','G7-ORIGINAL-BOUNDARY-NATIVE-FIXTURES',
        'G7-EXECUTABLE-INITIALIZATION-COEFFICIENTS','G7-SINGLE-EPOCH-TABLE-IDENTITY',
        'G7-CONCRETE-ORIGINAL-NODE-COEFFICIENTS']:
        record=next(r for r in records if r['id']==key)
        if record['status'].startswith('new_kernel_checked'):
            record['genuinely_remaining']=[
                'Generated-calendar date/phase/interval-occurrence refinement and terminal support remain separate',
                'General native encoding/normalization/dictionary/resource-cap and universal Rust refinement remain open']
            record['checked_word_composition']='G7-CONCRETE-ORIGINAL-WORD-COEFFICIENTS'
    generic=next(r for r in records if r['id']=='G7-SPARSE-WORD-COMPOSITION')
    generic['genuinely_remaining']=[
        'Exact per-step coefficient identity remains an explicit premise; the separate concrete original-word theorem supplies it',
        'Generated-calendar refinement, terminal support and general native dictionary/resource-cap refinement remain separate']
    policy=next(r for r in records if r['id']=='G7-POLICY-MASTER')
    policy['genuinely_remaining']=[
        'Exact original cofacial admission and independent whole-edge source-family coverage',
        'Generated-calendar and terminal-support consumers of the checked sparse word coefficient composition',
        'Complete same-source Winning syntax and effective real QE, with action/lower-witness selection relative to the actual history field',
        'Exact Pareto/policy/certificate producer; checked semantic and coefficient dependencies do not supply an effective producer']
completed_word=next(r for r in records if r['id']=='G7-CONCRETE-ORIGINAL-COMPLETED-WORD-COEFFICIENTS')
if completed_word['status']=='new_kernel_checked_exact_source':
    word['genuinely_remaining']=[
        'Generated-calendar date/phase/interval-occurrence refinement and every-raw-endpoint ancestral support remain separate',
        'Universal native encoding/normalization and runtime dictionary/cap correspondence remain separate']
    for key in ['G7-SUPPORT-ANCESTRAL-COMPLETION','G7-ORIGINAL-COMPLETION-NATIVE-FIXTURES']:
        record=next(r for r in records if r['id']==key)
        if record['status'].startswith('new_kernel_checked'):
            record['genuinely_remaining']=[
                'Every-raw-endpoint ancestral support for generated calendars remains separate',
                'General native encoding/normalization/dictionary and terminal-wrapper refinement remain separate']
            record['checked_conditional_word_composition']='G7-CONCRETE-ORIGINAL-COMPLETED-WORD-COEFFICIENTS'
fixture=next(r for r in records if r['id']=='G7-ORIGINAL-POPULATION-NATIVE-FIXTURES')
if execution_path.exists() and fixture['status']=='new_kernel_checked_exact_source':
    execution=json.loads(execution_path.read_text())
    expected={'emptyEdge0','oneAncestral','twoAncestral','threeEdge0','fourAncestral',
        'carriedNonminimum','permutedRestrictedEdge0','frozenRegisterRepeat'}
    runs={r['fixture']:r for r in execution['records']}
    if (execution['status']=='PASS_EIGHT_IMPORTED_ORIGINAL_COEFFICIENT_EXECUTIONS'
        and execution['source_and_import_artifacts_stable']
        and execution['fixture_source_sha256']==fixture['providers'][0]['sha256']
        and set(runs)==expected and all(r['exit_code']==0 for r in runs.values())):
        fixture['status']='new_kernel_checked_and_eight_imported_evaluations_pass'
        fixture['evidence'].append(str(execution_path.relative_to(ROOT)))
        fixture['execution_mode']=execution['execution_mode']
        fixture['standalone_native_elf_claimed']=execution['standalone_native_elf_claimed']
        fixture['genuinely_remaining']=[
            'Independent eight-fixture Lean/Rust/spectral-oracle comparison remains pending',
            'Generic normalized dictionary/serialization equality and universal Code-to-LAW quotient theorem remain separate']
        if comparison_path.exists():
            comparison=json.loads(comparison_path.read_text())
            cases={c['fixture']:c for c in comparison['cases']}
            if (comparison['pass'] and comparison['cases_passed']==8
                and comparison['cases_total']==8 and set(cases)==expected
                and comparison['binary_pins_before']==comparison['binary_pins_after']
                and comparison['observed_input_pins_before']==comparison['observed_input_pins_after']
                and all(c['pass'] and not c['errors']
                    and c['process_runs']['lean']['exit_code']==0
                    and c['process_runs']['rust']['exit_code']==0
                    and c['process_runs']['lean']['stdout_sha256']==runs[name]['stdout_sha256']
                    for name,c in cases.items())):
                fixture['status']='new_kernel_checked_and_eight_finite_original_comparisons_pass'
                fixture['evidence'].append(str(comparison_path.relative_to(ROOT)))
                fixture['finite_comparison']={
                    'cases_passed':8,'cases_total':8,
                    'execution_modes':comparison['execution_modes'],
                    'oracle_algorithm':comparison['oracle_algorithm'],
                    'general_refinement_proof_claimed':False}
                fixture['genuinely_remaining']=[
                    'Generic normalized dictionary/serialization equality and universal Code-to-LAW quotient theorem remain separate',
                    'Full epoch population-panel extraction and universal Rust refinement remain separate']
result={'schema':'commons-obligation-reuse-map-v1','contributor':'Codex / lean_reuse_recovery and lean_reuse_successor','created_utc':'2026-10-10','snapshot_kind':'source-read audit plus exact fresh kernel receipts where matched','source_hashes_checked':True,
 'global_constraints':['No sorry/admitted/custom axioms authorized','Inherited receipts remain attached only to their exact prior source/import context','Build/module counts do not establish master mathematical completion','Generic matrix/theorem validity does not supply biological measurement admission','Finite registry/rational chart exclusion is not unknown-size G3 NO coverage'],
 'obligations':records}
(HERE/'OBLIGATION-REUSE-MAP.json').write_text(json.dumps(result,indent=2)+'\n')
print(f'{len(records)} obligations; {sum(len(r["providers"]) for r in records)} hashed source references; all named source declarations found')
