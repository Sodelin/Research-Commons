import Lean
set_option warningAsError true
namespace ProofBridge

def sign (i : Nat) : Int := (i : Int) - 1
def goldbachPair (i j : Nat) : Int :=
  (if sign i != 0 then sign j else 0) - (if sign j != 0 then sign i else 0)
def row (i j : Nat) : Int :=
  if sign i * sign j == -1 then 2 * sign j else 0

def actual : List Int :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => goldbachPair i j

def normalForm : List Int :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => row i j

theorem transpose_normal_form : actual = normalForm := by decide

theorem certificate_sound (proposed : List Int) (h : proposed = actual) :
    proposed = normalForm := h.trans transpose_normal_form

theorem signed_count_arithmetic (p e o c l : Int)
    (hc : c = p + e + o) (hl : l = p + e - o) : c + l = 2 * (p + e) := by omega
end ProofBridge

#print axioms ProofBridge.transpose_normal_form
#print axioms ProofBridge.certificate_sound
#print axioms ProofBridge.signed_count_arithmetic

