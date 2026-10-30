import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

set_option debug.skipKernelTC false
/-! Ordered physical-tip trees and a sound compositional finite certificate.
The syntax is rooted at one distinguished external pendant occurrence.
No statement about a source network's embedding/order is assumed or proved.
-/
namespace Nanuq.AdjacentCertificate

inductive Tree where
  | tip : Tree
  | fork : Tree → Tree → Tree
  deriving DecidableEq, Repr

def Tree.size : Tree → Nat
  | .tip => 1
  | .fork a b => a.size + b.size

theorem Tree.size_pos (t : Tree) : 0 < t.size := by
  induction t with
  | tip => decide
  | fork a b ha hb => simp only [size]; omega

/-- Union of all internal-edge quartet witnesses, encoded as bit sets.
An internal interval is included even at the root; its complement there
is the distinguished tip, so the actual contribution is zero. -/
def Tree.summary (edgeContribution : Nat → Nat → Nat) (lo : Nat) : Tree → Nat
  | .tip => 0
  | .fork a b =>
    a.summary edgeContribution lo ||| b.summary edgeContribution (lo + a.size) |||
      edgeContribution lo (a.size + b.size)

abbrev Table := Nat → Nat → List Nat

/-- Closure of a finite table under the actual interval-tree recurrence. -/
def Closed (c : Nat → Nat → Nat) (m : Nat) (table : Table) : Prop :=
  (∀ lo, lo < m → 0 ∈ table lo 1) ∧
  (∀ lo len, 2 ≤ len → lo + len ≤ m →
    ∀ k, 0 < k → k < len → ∀ a ∈ table lo k, ∀ b ∈ table (lo+k) (len-k),
      (a ||| b ||| c lo len) ∈ table lo len)

/-- Structural induction proves representation coverage. Certificate lists
may overapproximate; no imported claim that their positives are exhaustive
is trusted. -/
theorem summary_mem (c : Nat → Nat → Nat) (m : Nat) (table : Table)
    (hc : Closed c m table) (t : Tree) (lo : Nat) (bound : lo + t.size ≤ m) :
    t.summary c lo ∈ table lo t.size := by
  induction t generalizing lo with
  | tip => exact hc.1 lo (by simp only [Tree.size] at bound; omega)
  | fork a b ha hb =>
    have hpa := a.size_pos
    have hpb := b.size_pos
    have hbound : lo + (a.size + b.size) ≤ m := bound
    have hA := ha lo (by omega)
    have hB := hb (lo+a.size) (by omega)
    have he : a.size + b.size - a.size = b.size := by omega
    simpa only [Tree.summary, Tree.size, he] using
      hc.2 lo (a.size+b.size) (by omega) hbound a.size hpa (by omega) _ hA _ (by simpa only [he] using hB)

def checkClosed (c : Nat → Nat → Nat) (m : Nat) (table : Table) : Bool :=
  (List.range m).all (fun lo => decide (0 ∈ table lo 1)) &&
  (List.range m).all (fun lo => (List.range (m+1)).all (fun len =>
    if 2 ≤ len ∧ lo+len ≤ m then
      (List.range len).all (fun k => if 0 < k then
        (table lo k).all (fun a => (table (lo+k) (len-k)).all
          (fun b => decide ((a ||| b ||| c lo len) ∈ table lo len)))
      else true)
    else true))

theorem closed_of_check (c : Nat → Nat → Nat) (m : Nat) (table : Table)
    (h : checkClosed c m table = true) : Closed c m table := by
  simp only [checkClosed, Bool.and_eq_true, List.all_eq_true] at h
  constructor
  · intro lo hlo
    exact of_decide_eq_true (h.1 lo (List.mem_range.mpr hlo))
  · intro lo len hlen hbound k hk hklen a ha b hb
    have hlo : lo < m := by omega
    have hlenm : len < m+1 := by omega
    have hh := h.2 lo (List.mem_range.mpr hlo) len (List.mem_range.mpr hlenm)
    have hcond : 2 ≤ len ∧ lo+len ≤ m := ⟨hlen,hbound⟩
    simp only [if_pos hcond, List.all_eq_true] at hh
    have hh := hh k (List.mem_range.mpr hklen)
    simp only [if_pos hk, List.all_eq_true] at hh
    exact of_decide_eq_true (hh a ha b hb)

/-- Any Boolean property checked on the table holds on EVERY ordered tree
of the specified size, by the derived closure rather than enumeration trust. -/
theorem property_of_certificate (c : Nat → Nat → Nat) (m : Nat) (table : Table)
    (h : checkClosed c m table = true) (lo len : Nat)
    (test : Nat → Bool) (ht : (table lo len).all test = true)
    (t : Tree) (hs : t.size = len) (bound : lo+len ≤ m) :
    test (t.summary c lo) = true := by
  apply List.all_eq_true.mp ht
  have hh := summary_mem c m table (closed_of_check c m table h) t lo (by simpa [hs] using bound)
  simpa only [hs] using hh

#print axioms summary_mem
#print axioms closed_of_check
#print axioms property_of_certificate
end Nanuq.AdjacentCertificate
