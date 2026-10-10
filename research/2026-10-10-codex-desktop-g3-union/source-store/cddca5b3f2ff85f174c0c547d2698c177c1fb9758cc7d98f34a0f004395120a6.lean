import G6RationalCompressionCertificate

/-!
# Typed finite certificates from the saved private Rust compressor

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Every literal input and output below comes from the independently retained
rust/evidence/rational-compression-review-2 request/result pairs. The companion
capture pins those exact JSON bytes, checker receipts and the private binary.
No producer is reexecuted here. `sameMassWrongTail` is a deliberately forged
positive certificate, with the original indices and total mass unchanged.

These are finite compiled Boolean checks of the accepted mathematical checker.
They do not prove general native JSON/parser or RREF refinement, resource
exhaustion, arbitrary-real extraction, calendar exposure representation or
legal positive source reconstruction. Draft pending sole-scheduler checks.
-/

namespace GProgram.G6.RationalCompressionCertificateFixture

open GProgram.G6.RationalCompressionCertificate
open scoped BigOperators

/-- Exact saved `historicalM2` data: M=2, 6 original atoms and 1 selected indices. -/
def historicalM2_z (a : Fin 6) : ℚ :=
  if a.val = 0 then ((1 : ℚ) / 7) else
    if a.val = 1 then ((2 : ℚ) / 7) else
    if a.val = 2 then ((3 : ℚ) / 7) else
    if a.val = 3 then ((4 : ℚ) / 7) else
    if a.val = 4 then ((5 : ℚ) / 7) else
    ((6 : ℚ) / 7)

def historicalM2_alpha (a : Fin 6) : ℚ :=
  if a.val = 0 then ((2 : ℚ) / 3) else
    if a.val = 1 then ((3 : ℚ) / 4) else
    if a.val = 2 then ((4 : ℚ) / 5) else
    if a.val = 3 then ((5 : ℚ) / 6) else
    if a.val = 4 then ((6 : ℚ) / 7) else
    ((7 : ℚ) / 8)

def historicalM2_atom (a : Fin 1) : Fin 6 :=
  ⟨0, by decide⟩

def historicalM2_beta (a : Fin 1) : ℚ :=
  ((1339 : ℚ) / 280)

def historicalM2_check : Bool :=
  checkCompression 2 historicalM2_z historicalM2_alpha historicalM2_atom historicalM2_beta

/-- Exact saved `historicalM3` data: M=3, 7 original atoms and 2 selected indices. -/
def historicalM3_z (a : Fin 7) : ℚ :=
  if a.val = 0 then ((1 : ℚ) / 8) else
    if a.val = 1 then ((1 : ℚ) / 4) else
    if a.val = 2 then ((3 : ℚ) / 8) else
    if a.val = 3 then ((1 : ℚ) / 2) else
    if a.val = 4 then ((5 : ℚ) / 8) else
    if a.val = 5 then ((3 : ℚ) / 4) else
    ((7 : ℚ) / 8)

def historicalM3_alpha (a : Fin 7) : ℚ :=
  if a.val = 0 then ((2 : ℚ) / 3) else
    if a.val = 1 then ((3 : ℚ) / 4) else
    if a.val = 2 then ((4 : ℚ) / 5) else
    if a.val = 3 then ((5 : ℚ) / 6) else
    if a.val = 4 then ((6 : ℚ) / 7) else
    if a.val = 5 then ((7 : ℚ) / 8) else
    ((8 : ℚ) / 9)

def historicalM3_atom (a : Fin 2) : Fin 7 :=
  if a.val = 0 then ⟨2, by decide⟩ else
    ⟨4, by decide⟩

def historicalM3_beta (a : Fin 2) : ℚ :=
  if a.val = 0 then ((21121 : ℚ) / 11520) else
    ((6877 : ℚ) / 1792)

def historicalM3_check : Bool :=
  checkCompression 3 historicalM3_z historicalM3_alpha historicalM3_atom historicalM3_beta

/-- Exact saved `historicalM4` data: M=4, 8 original atoms and 3 selected indices. -/
def historicalM4_z (a : Fin 8) : ℚ :=
  if a.val = 0 then ((1 : ℚ) / 9) else
    if a.val = 1 then ((2 : ℚ) / 9) else
    if a.val = 2 then ((1 : ℚ) / 3) else
    if a.val = 3 then ((4 : ℚ) / 9) else
    if a.val = 4 then ((5 : ℚ) / 9) else
    if a.val = 5 then ((2 : ℚ) / 3) else
    if a.val = 6 then ((7 : ℚ) / 9) else
    ((8 : ℚ) / 9)

def historicalM4_alpha (a : Fin 8) : ℚ :=
  if a.val = 0 then ((2 : ℚ) / 3) else
    if a.val = 1 then ((3 : ℚ) / 4) else
    if a.val = 2 then ((4 : ℚ) / 5) else
    if a.val = 3 then ((5 : ℚ) / 6) else
    if a.val = 4 then ((6 : ℚ) / 7) else
    if a.val = 5 then ((7 : ℚ) / 8) else
    if a.val = 6 then ((8 : ℚ) / 9) else
    ((9 : ℚ) / 10)

def historicalM4_atom (a : Fin 3) : Fin 8 :=
  if a.val = 0 then ⟨0, by decide⟩ else
    if a.val = 1 then ⟨5, by decide⟩ else
    ⟨7, by decide⟩

def historicalM4_beta (a : Fin 3) : ℚ :=
  if a.val = 0 then ((5713724 : ℚ) / 2724795) else
    if a.val = 1 then ((191775767 : ℚ) / 50862840) else
    ((2982449 : ℚ) / 4238570)

def historicalM4_check : Bool :=
  checkCompression 4 historicalM4_z historicalM4_alpha historicalM4_atom historicalM4_beta

/-- Exact saved `empty` data: M=4, 0 original atoms and 0 selected indices. -/
def empty_z : Fin 0 → ℚ := Fin.elim0

def empty_alpha : Fin 0 → ℚ := Fin.elim0

def empty_atom : Fin 0 → Fin 0 := Fin.elim0

def empty_beta : Fin 0 → ℚ := Fin.elim0

def empty_check : Bool :=
  checkCompression 4 empty_z empty_alpha empty_atom empty_beta

/-- Exact saved `allZero` data: M=4, 2 original atoms and 0 selected indices. -/
def allZero_z (a : Fin 2) : ℚ :=
  if a.val = 0 then ((1 : ℚ) / 3) else
    ((2 : ℚ) / 3)

def allZero_alpha (a : Fin 2) : ℚ :=
  if a.val = 0 then (0 : ℚ) else
    (0 : ℚ)

def allZero_atom : Fin 0 → Fin 2 := Fin.elim0

def allZero_beta : Fin 0 → ℚ := Fin.elim0

def allZero_check : Bool :=
  checkCompression 4 allZero_z allZero_alpha allZero_atom allZero_beta

/-- Exact saved `sameMassWrongTail` data: M=3, 7 original atoms and 2 selected indices. -/
def sameMassWrongTail_z (a : Fin 7) : ℚ :=
  if a.val = 0 then ((1 : ℚ) / 8) else
    if a.val = 1 then ((1 : ℚ) / 4) else
    if a.val = 2 then ((3 : ℚ) / 8) else
    if a.val = 3 then ((1 : ℚ) / 2) else
    if a.val = 4 then ((5 : ℚ) / 8) else
    if a.val = 5 then ((3 : ℚ) / 4) else
    ((7 : ℚ) / 8)

def sameMassWrongTail_alpha (a : Fin 7) : ℚ :=
  if a.val = 0 then ((2 : ℚ) / 3) else
    if a.val = 1 then ((3 : ℚ) / 4) else
    if a.val = 2 then ((4 : ℚ) / 5) else
    if a.val = 3 then ((5 : ℚ) / 6) else
    if a.val = 4 then ((6 : ℚ) / 7) else
    if a.val = 5 then ((7 : ℚ) / 8) else
    ((8 : ℚ) / 9)

def sameMassWrongTail_atom (a : Fin 2) : Fin 7 :=
  if a.val = 0 then ⟨2, by decide⟩ else
    ⟨4, by decide⟩

def sameMassWrongTail_beta (a : Fin 2) : ℚ :=
  if a.val = 0 then ((528313 : ℚ) / 288000) else
    ((859401 : ℚ) / 224000)

def sameMassWrongTail_check : Bool :=
  checkCompression 3 sameMassWrongTail_z sameMassWrongTail_alpha sameMassWrongTail_atom sameMassWrongTail_beta

/-- The negative control has the same mass and all nonmoment premises. -/
def wrongTail_massPreserved : Bool := decide
  ((∑ b : Fin 2, sameMassWrongTail_beta b) =
    ∑ a : Fin 7, sameMassWrongTail_alpha a)

def wrongTail_nonMomentPremises : Bool := decide
  ((2 : ℕ) ≤ 3 ∧
    (∀ a : Fin 7, 0 < sameMassWrongTail_z a ∧ sameMassWrongTail_z a < 1) ∧
    (∀ a : Fin 7, 0 ≤ sameMassWrongTail_alpha a) ∧
    (2 : ℕ) ≤ 3 - 1 ∧ (∀ b : Fin 2, 0 < sameMassWrongTail_beta b))

def wrongTail_tailDiffers : Bool := decide
  ((∑ a : Fin 7, sameMassWrongTail_alpha a * rationalGeometricSum 3 (sameMassWrongTail_z a)) ≠
    ∑ b : Fin 2, sameMassWrongTail_beta b *
      rationalGeometricSum 3 (sameMassWrongTail_z (sameMassWrongTail_atom b)))

/-- Actual Boolean results and their independently retained expected values. -/
def checks : List (String × Bool × Bool) :=
  [
    ("historicalM2", historicalM2_check, true),
    ("historicalM3", historicalM3_check, true),
    ("historicalM4", historicalM4_check, true),
    ("empty", empty_check, true),
    ("allZero", allZero_check, true),
    ("sameMassWrongTail", sameMassWrongTail_check, false),
    ("wrongTailMass", wrongTail_massPreserved, true),
    ("wrongTailOtherPremises", wrongTail_nonMomentPremises, true),
    ("wrongTailMomentDiffers", wrongTail_tailDiffers, true) ]

def allChecksPass : Bool := checks.all (fun (_, actual, expected) => actual == expected)

#eval checks
#guard allChecksPass

#print axioms checks

end GProgram.G6.RationalCompressionCertificateFixture
