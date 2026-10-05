import UnifiedLean.Source.E8SCFG2PartnerAdmission

/-!
# Validated round-scaffold scanner versus independent structural specification

The open/push, close/write/pop and x-write control flow is from public
TakumiOtagaki/PKProbDesign27af, submodules/CParty/src/sparse_tree.cc96--123.
The independent specification is the usual balanced round-word grammar.
This is the pair-assignment projection of the loop, not a proof of its raw
C++ parent pointers, RMQ preprocessing, resources or memory safety.
-/
namespace UnifiedLean.Source.E8SCFG2ScaffoldScan
open scoped Classical

inductive Token where
  | openRound | closeRound | dot | forced
  deriving DecidableEq

/-- Independent recursive specification of a balanced .x() scaffold. -/
inductive RoundWord where
  | empty
  | unpaired (forced : Bool) (rest : RoundWord)
  | paired (inside rest : RoundWord)
  deriving DecidableEq

def width : RoundWord → ℕ
  | .empty => 0
  | .unpaired _ rest => 1 + width rest
  | .paired inside rest => 2 + width inside + width rest

def tokens : RoundWord → List Token
  | .empty => []
  | .unpaired forced rest => (if forced then Token.forced else Token.dot) :: tokens rest
  | .paired inside rest => Token.openRound :: (tokens inside ++ Token.closeRound :: tokens rest)

theorem tokens_length (word : RoundWord) : (tokens word).length = width word := by
  induction word with
  | empty => rfl
  | unpaired forced rest ih => simp [tokens,width,ih]; omega
  | paired inside rest ih1 ih2 => simp [tokens,width,ih1,ih2]; omega

inductive RawAction where
  | close (openPosition closePosition : ℕ)
  | forcedUnpaired (position : ℕ)
  deriving DecidableEq

structure ScanState where
  next : ℕ
  stack : List ℕ
  actions : List RawAction
  deriving DecidableEq

/-- Literal pair-table write projection of one loop iteration. A close uses
stack.back, records the symmetric assignment, then pops. Empty-stack failure
is outside validated RoundWord scans. Position0 is the initial source sentinel. -/
def step (st : ScanState) : Token → Option ScanState
  | .openRound => some ⟨st.next+1,st.next::st.stack,st.actions⟩
  | .dot => some ⟨st.next+1,st.stack,st.actions⟩
  | .forced => some ⟨st.next+1,st.stack,st.actions++[.forcedUnpaired st.next]⟩
  | .closeRound => match st.stack with
    | [] => none
    | k::ks => some ⟨st.next+1,ks,st.actions++[.close k st.next]⟩

def scan : List Token → ScanState → Option ScanState
  | [], st => some st
  | t::ts, st => (step st t).bind (scan ts)

/-- Actual ASCII symbols read by sparse_tree::create_tree. -/
def tokenChar : Token → Char
  | .openRound => '(' | .closeRound => ')' | .dot => '.' | .forced => 'x'

/-- Literal character tests projected onto pair writes/stack. Unrecognized
characters have the source's unchanged pair state; admitted words use .x(). -/
def characterStep (st : ScanState) (c : Char) : Option ScanState :=
  if c = 'x' then some ⟨st.next+1,st.stack,st.actions++[.forcedUnpaired st.next]⟩
  else if c = ')' then match st.stack with
    | [] => none
    | k::ks => some ⟨st.next+1,ks,st.actions++[.close k st.next]⟩
  else if c = '(' then some ⟨st.next+1,st.next::st.stack,st.actions⟩
  else some ⟨st.next+1,st.stack,st.actions⟩

private theorem character_step_token (st : ScanState) (t : Token) :
    characterStep st (tokenChar t) = step st t := by
  cases t <;> simp [tokenChar,characterStep,step]

def scanCharacters : List Char → ScanState → Option ScanState
  | [], st => some st
  | c::cs, st => (characterStep st c).bind (scanCharacters cs)

theorem character_scan_serialize (ts : List Token) (st : ScanState) :
    scanCharacters (ts.map tokenChar) st = scan ts st := by
  induction ts generalizing st with
  | nil => rfl
  | cons t ts ih => simp [scanCharacters,scan,character_step_token,ih]

private theorem scan_append (a b : List Token) (st : ScanState) :
    scan (a++b) st = (scan a st).bind (scan b) := by
  induction a generalizing st with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.cons_append,scan]
    cases h : step st t with
    | none => rfl
    | some s => simpa only [h,Option.bind_some] using ih s

/-- Specification of expected closing actions: nested closes precede their
own outer close, exactly as the loop visits the closing symbols. -/
def specActions : RoundWord → ℕ → List RawAction
  | .empty, _ => []
  | .unpaired forced rest, start =>
      (if forced then [.forcedUnpaired start] else []) ++ specActions rest (start+1)
  | .paired inside rest, start =>
      specActions inside (start+1) ++ [.close start (start+width inside+1)] ++
        specActions rest (start+width inside+2)

/-- Total validated scanner theorem, retaining the actual incoming stack
and earlier write order. No balanced-scan result is an admission field. -/
theorem scan_balanced (word : RoundWord) (start : ℕ) (stack : List ℕ)
    (previous : List RawAction) :
    scan (tokens word) ⟨start,stack,previous⟩ =
      some ⟨start+width word,stack,previous++specActions word start⟩ := by
  induction word generalizing start stack previous with
  | empty => simp [tokens,scan,width,specActions]
  | unpaired forced rest ih =>
    cases forced <;> simp [tokens,scan,step,width,specActions,ih,List.append_assoc,Nat.add_assoc]
  | paired inside rest ih1 ih2 =>
    simp only [tokens,scan,step,Option.bind_some]
    rw [scan_append,ih1]
    simp only [Option.bind_some,scan,step]
    rw [ih2]
    simp [width,specActions,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    constructor
    · omega
    · congr 1; omega

/-- Independently specified structural scaffold pairs. This uses tree
nesting directly, not the scanner's output/table as a definition. -/
def paperPairs : RoundWord → ℕ → List (ℕ × ℕ)
  | .empty, _ => []
  | .unpaired _ rest, start => paperPairs rest (start+1)
  | .paired inside rest, start =>
      (start,start+width inside+1) ::
        (paperPairs inside (start+1) ++ paperPairs rest (start+width inside+2))

theorem close_action_iff_paper_pair (word : RoundWord) (start x y : ℕ) :
    RawAction.close x y ∈ specActions word start ↔ (x,y) ∈ paperPairs word start := by
  induction word generalizing start with
  | empty => simp [specActions,paperPairs]
  | unpaired forced rest ih =>
    cases forced <;> simp [specActions,paperPairs,ih]
  | paired inside rest ih1 ih2 =>
    simp [specActions,paperPairs,ih1,ih2,or_left_comm,Prod.mk.injEq]

/-- Exact source-domain bounds for every action, sufficient to construct
Fin n without clipping after the root length is matched. -/
def Within (start count : ℕ) : RawAction → Prop
  | .close x y => start ≤ x ∧ x < y ∧ y < start+count
  | .forcedUnpaired x => start ≤ x ∧ x < start+count

theorem spec_actions_within (word : RoundWord) (start : ℕ) (action : RawAction)
    (ha : action ∈ specActions word start) : Within start (width word) action := by
  induction word generalizing start action with
  | empty => simp [specActions] at ha
  | unpaired forced rest ih =>
    cases forced with
    | false =>
      simp only [specActions,Bool.false_eq_true,↓reduceIte,List.nil_append] at ha
      have h := ih (start+1) action ha
      cases action <;> simp only [Within,width] at h ⊢ <;> omega
    | true =>
      simp only [specActions,↓reduceIte,List.singleton_append,List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [Within,width]
      · have h := ih (start+1) action ha
        cases action <;> simp only [Within,width] at h ⊢ <;> omega
  | paired inside rest ih1 ih2 =>
    simp only [specActions,List.mem_append,List.mem_singleton] at ha
    rcases ha with (ha | rfl) | ha
    · have h := ih1 (start+1) action ha
      cases action <;> simp only [Within,width] at h ⊢ <;> omega
    · simp [Within,width]; omega
    · have h := ih2 (start+width inside+2) action ha
      cases action <;> simp only [Within,width] at h ⊢ <;> omega

private theorem paper_pair_within (word : RoundWord) (start : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ paperPairs word start) : start ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < start+width word := by
  have ha := (close_action_iff_paper_pair word start p.1 p.2).mpr hp
  exact spec_actions_within word start (.close p.1 p.2) ha

/-- Structural x positions cannot be endpoints of any independently
specified scaffold pair. This is derived from the word, not supplied metadata. -/
theorem forced_avoids_paper_endpoints (word : RoundWord) (start k : ℕ)
    (hk : RawAction.forcedUnpaired k ∈ specActions word start)
    (p : ℕ × ℕ) (hp : p ∈ paperPairs word start) : k ≠ p.1 ∧ k ≠ p.2 := by
  induction word generalizing start k p with
  | empty => simp [specActions] at hk
  | unpaired forced rest ih =>
    cases forced with
    | false =>
      simp [specActions] at hk
      exact ih (start+1) k hk p hp
    | true =>
      simp [specActions] at hk
      rcases hk with rfl | hk
      · have h := paper_pair_within rest (k+1) p hp
        constructor <;> omega
      · exact ih (start+1) k hk p hp
  | paired inside rest ih1 ih2 =>
    simp [specActions] at hk
    simp only [paperPairs,List.mem_cons,List.mem_append] at hp
    rcases hk with hk | hk
    · have hi := spec_actions_within inside (start+1) (.forcedUnpaired k) hk
      change start+1 ≤ k ∧ k < start+1+width inside at hi
      rcases hp with rfl | hp | hp
      · constructor <;> omega
      · exact ih1 (start+1) k hk p hp
      · have hr := paper_pair_within rest (start+width inside+2) p hp
        constructor <;> omega
    · have hr := spec_actions_within rest (start+width inside+2) (.forcedUnpaired k) hk
      change start+width inside+2 ≤ k ∧ k < start+width inside+2+width rest at hr
      rcases hp with rfl | hp | hp
      · constructor <;> omega
      · have hi := paper_pair_within inside (start+1) p hp
        constructor <;> omega
      · exact ih2 (start+width inside+2) k hk p hp

/-- Literal initial source sentinel is preserved by the entire balanced
scan, and all expected closes are the independently specified pairs. -/
theorem validated_initial_scan (word : RoundWord) :
    scan (tokens word) ⟨1,[0],[]⟩ =
      some ⟨1+width word,[0],specActions word 1⟩ := by
  simpa using scan_balanced word 1 [0] []

theorem character_scan_balanced (word : RoundWord) :
    scanCharacters ((tokens word).map tokenChar) ⟨1,[0],[]⟩ =
      some ⟨1+width word,[0],specActions word 1⟩ := by
  rw [character_scan_serialize]
  exact validated_initial_scan word

open UnifiedLean.Source.E8PaperGammaAdmission
open UnifiedLean.Source.E8SCFG2RootEventDecoder
open UnifiedLean.Source.E8SCFG2PartnerAdmission

variable {n : ℕ}

/-- Independent encoding of the already fixed paper scaffold as a balanced
round word. Membership uses structural paperPairs, not parser/table output. -/
structure RoundEncoding (G : Structure n) (word : RoundWord) where
  length : width word = n
  membership : ∀ p : Pair n,
    p ∈ G ↔ (p.1.val+1,p.2.val+1) ∈ paperPairs word 1

private def closePair (word : RoundWord) (hn : width word = n) (x y : ℕ)
    (ha : RawAction.close x y ∈ specActions word 1) : Pair n := by
  have hb := spec_actions_within word 1 (.close x y) ha
  change 1 ≤ x ∧ x < y ∧ y < 1+width word at hb
  exact (positionIndex n (x : ℤ) (by omega) (by omega),
    positionIndex n (y : ℤ) (by omega) (by omega))

private theorem closePair_exact (word : RoundWord) (hn : width word = n) (x y : ℕ)
    (ha : RawAction.close x y ∈ specActions word 1) :
    (closePair word hn x y ha).1.val+1 = x ∧
    (closePair word hn x y ha).2.val+1 = y := by
  have hb := spec_actions_within word 1 (.close x y) ha
  change 1 ≤ x ∧ x < y ∧ y < 1+width word at hb
  constructor
  · have h := positionIndex_roundtrip n (x : ℤ) (by omega) (by omega)
    exact_mod_cast h
  · have h := positionIndex_roundtrip n (y : ℤ) (by omega) (by omega)
    exact_mod_cast h

private def forcedPosition (word : RoundWord) (hn : width word = n) (x : ℕ)
    (ha : RawAction.forcedUnpaired x ∈ specActions word 1) : Fin n := by
  have hb := spec_actions_within word 1 (.forcedUnpaired x) ha
  change 1 ≤ x ∧ x < 1+width word at hb
  exact positionIndex n (x : ℤ) (by omega) (by omega)

private theorem forcedPosition_exact (word : RoundWord) (hn : width word = n) (x : ℕ)
    (ha : RawAction.forcedUnpaired x ∈ specActions word 1) :
    (forcedPosition word hn x ha).val+1 = x := by
  have hb := spec_actions_within word 1 (.forcedUnpaired x) ha
  change 1 ≤ x ∧ x < 1+width word at hb
  have h := positionIndex_roundtrip n (x : ℤ) (by omega) (by omega)
  exact_mod_cast h

/-- Coordinates are constructed using proven source bounds, preserving each
ordered write occurrence. There is no modulo/clipping fallback. -/
def boundRawAction (word : RoundWord) (hn : width word = n)
    (a : {a : RawAction // a ∈ specActions word 1}) : PairAction n :=
  match a with
  | ⟨.close x y,ha⟩ => .close (closePair word hn x y ha)
  | ⟨.forcedUnpaired x,ha⟩ => .forcedUnpaired (forcedPosition word hn x ha)

def boundedActions (word : RoundWord) (hn : width word = n) : List (PairAction n) :=
  (specActions word 1).attach.map (boundRawAction word hn)

/-- Constructs the previously missing ClosingAdmission from the validated
scanner's independent bracket specification. Allowed/x/coverage fields are
PROVED here, not requested anew as desired table correctness. -/
def closingAdmissionFromEncoding (G : Structure n) (word : RoundWord)
    (enc : RoundEncoding G word) : ClosingAdmission G where
  actions := boundedActions word enc.length
  allowed := by
    intro a ha
    obtain ⟨raw,hm,rfl⟩ := List.mem_map.mp ha
    rcases raw with ⟨raw,hr⟩
    cases raw with
    | close x y =>
      change closePair word enc.length x y hr ∈ G
      apply (enc.membership _).mpr
      have hc := closePair_exact word enc.length x y hr
      rw [hc.1,hc.2]
      exact (close_action_iff_paper_pair word 1 x y).mp hr
    | forcedUnpaired x =>
      change ∀ p ∈ G,
        forcedPosition word enc.length x hr ≠ p.1 ∧ forcedPosition word enc.length x hr ≠ p.2
      intro p hp
      have hm := (enc.membership p).mp hp
      have hd := forced_avoids_paper_endpoints word 1 x hr
        (p.1.val+1,p.2.val+1) hm
      have hx := forcedPosition_exact word enc.length x hr
      constructor
      · intro he
        apply hd.1
        have hv := congrArg Fin.val he
        omega
      · intro he
        apply hd.2
        have hv := congrArg Fin.val he
        omega
  covers := by
    intro p hp
    have hm := (enc.membership p).mp hp
    have ha := (close_action_iff_paper_pair word 1 (p.1.val+1) (p.2.val+1)).mpr hm
    change PairAction.close p ∈ (specActions word 1).attach.map (boundRawAction word enc.length)
    refine List.mem_map.mpr ⟨⟨.close (p.1.val+1) (p.2.val+1),ha⟩,by simp,?_⟩
    change PairAction.close (closePair word enc.length (p.1.val+1) (p.2.val+1) ha) = .close p
    have hc := closePair_exact word enc.length (p.1.val+1) (p.2.val+1) ha
    congr 1
    apply Prod.ext
    · apply Fin.ext; omega
    · apply Fin.ext; omega

/-- Complete represented partner-kernel/generated-observable binding for
all balanced encoded inputs. Executed C++ equality, grammar/support/energy,
lossless renderer/classifier and numerical/RNG instances remain distinct. -/
theorem encoded_generated_stream_agreement (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (word : RoundWord) (enc : RoundEncoding G word)
    (events : List (SourceEvent n)) (hd : EmissionDomain events) :
    sourceGeneratedPairs
      (partnerFromTable (runActions (initialState n) (boundedActions word enc.length)).table) events =
      generatedPairs G events := by
  exact generated_stream_agreement seq G hs (closingAdmissionFromEncoding G word enc) events hd

/-- One coherent represented scanner→write-table→Γ-emission endpoint.
The same derived specActions feed both the proved character scan and table.
The actual C++ string/vector/pointer execution remains outside this theorem. -/
theorem encoded_scanner_pipeline (seq : Fin n → Base) (G : Structure n)
    (hs : Secondary seq G) (word : RoundWord) (enc : RoundEncoding G word)
    (events : List (SourceEvent n)) (hd : EmissionDomain events) :
    scanCharacters ((tokens word).map tokenChar) ⟨1,[0],[]⟩ =
      some ⟨1+width word,[0],specActions word 1⟩ ∧
    sourceGeneratedPairs
      (partnerFromTable (runActions (initialState n) (boundedActions word enc.length)).table) events =
      generatedPairs G events := by
  exact ⟨character_scan_balanced word,
    encoded_generated_stream_agreement seq G hs word enc events hd⟩

#print axioms tokens_length
#print axioms scan_balanced
#print axioms close_action_iff_paper_pair
#print axioms spec_actions_within
#print axioms forced_avoids_paper_endpoints
#print axioms validated_initial_scan
#print axioms character_scan_serialize
#print axioms character_scan_balanced
#print axioms closingAdmissionFromEncoding
#print axioms encoded_generated_stream_agreement
#print axioms encoded_scanner_pipeline
end UnifiedLean.Source.E8SCFG2ScaffoldScan
