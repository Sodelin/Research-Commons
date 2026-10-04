import ThueMorseMAP.Blocks
namespace ThueMorseMAP
open ThueMorseBits

theorem plus_before {m a b L k : ℕ} {c : Bool}
    (R : Run (a*2^m+b) (2^m+1) L c) (hk : k<L) (hb : b+k<2^m) :
    t (a+k)=Bool.xor c (t (b+k)) := by
  apply run_at (m:=m) R hk hb
  ring

theorem plus_after {m a b L k : ℕ} {c : Bool}
    (R : Run (a*2^m+b) (2^m+1) L c) (hk : k<L)
    (hb : 2^m≤b+k) (hb2 : b+k<2*2^m) :
    t (a+k+1)=Bool.xor c (t (b+k-2^m)) := by
  apply run_at (m:=m) R hk (by omega)
  have hsub := Nat.sub_add_cancel hb
  nlinarith

theorem plus_residue_options {m a b : ℕ} {c : Bool}
    (hm : 2≤m) (hb : b<2^m) (R : Run (a*2^m+b) (2^m+1) (2^m+2) c) :
    b=0 ∨ b=2^m-2 ∨ b=2^m-1 := by
  let q := 2^m
  have hq : 4≤q := pow_ge_four hm
  by_contra h
  have hb1 : 1≤b := by omega
  have hb3 : b≤q-3 := by omega
  have v0 := plus_before R (k:=q-b-3) (by omega) (by omega)
  have v1 := plus_before R (k:=q-b-2) (by omega) (by omega)
  have e0 : b+(q-b-3)=q-3 := by omega
  have e1 : b+(q-b-2)=q-2 := by omega
  rw [e0] at v0
  rw [e1] at v1
  dsimp [q] at v0 v1
  rw [tail_three hm] at v0
  rw [tail_two hm] at v1
  have he0 : t (a+(q-b-3))=t (a+(q-b-3)+1) := by
    have he : a+(q-b-3)+1=a+(q-b-2) := by omega
    rw [he]
    exact v0.trans v1.symm
  have v2 := plus_after R (k:=q-b+1) (by omega) (by omega) (by omega)
  have v3 := plus_after R (k:=q-b+2) (by omega) (by omega) (by omega)
  have e2 : b+(q-b+1)-q=1 := by omega
  have e3 : b+(q-b+2)-q=2 := by omega
  change t (a+(q-b+1)+1)=Bool.xor c (t (b+(q-b+1)-q)) at v2
  change t (a+(q-b+2)+1)=Bool.xor c (t (b+(q-b+2)-q)) at v3
  rw [e2,t_one] at v2
  rw [e3,t_two] at v3
  have he1 : t (a+(q-b+1)+1)=t ((a+(q-b+1)+1)+1) := by
    have he : (a+(q-b+1)+1)+1=a+(q-b+2)+1 := by omega
    rw [he]
    exact v2.trans v3.symm
  have ho0 := equal_adjacent_odd he0
  have ho1 := equal_adjacent_odd he1
  omega

/-- A full run's middle q terms force a recognized block. -/
theorem plus_final_block {m a : ℕ} {c : Bool}
    (hm : 2≤m) (R : Run (a*2^m+(2^m-1)) (2^m+1) (2^m+2) c) :
    Block m (a+2) c := by
  intro r hr
  have hq := pow_ge_four hm
  have v := plus_after R (k:=r+1) (by omega) (by omega) (by omega)
  have he : 2^m-1+(r+1)-2^m=r := by omega
  rw [he] at v
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using v

end ThueMorseMAP

namespace ThueMorseMAP
open ThueMorseBits

theorem half_plus_one {m : ℕ} (hm : 2≤m) : t (2^(m-1)+1)=false := by
  have hhalf : 1<2^(m-1) := by have := index_lt_two_pow (m-1); omega
  have h := t_dyadic_block 1 (m-1) 1 hhalf
  simpa using h

theorem plus_not_zero {m a : ℕ} {c : Bool} (hm : 2≤m)
    (R : Run (a*2^m+0) (2^m+1) (2^m+2) c) : False := by
  let q := 2^m
  have hq : 4≤q := pow_ge_four hm
  have B : Block m a c := by
    intro r hr
    simpa using plus_before R (k:=r) (by omega) (by omega)
  have v0 := plus_after R (k:=q) (by omega) (by omega) (by omega)
  have v1 := plus_after R (k:=q+1) (by omega) (by omega) (by omega)
  have e0 : 0+q-2^m=0 := by omega
  have e1 : 0+(q+1)-2^m=1 := by omega
  rw [e0,t_zero,Bool.xor_false] at v0
  rw [e1,t_one,xor_not] at v1
  have v1' : t (a+q+2)= !c := by simpa [Nat.add_assoc] using v1
  rcases block_cases hm B with ⟨l,hl,hc⟩ | ⟨l,hl,hc,hc1⟩
  · have e0 : a+q+1=(l+1)*q+1 := by change a=l*q at hl; nlinarith
    have e1 : a+q+2=(l+1)*q+2 := by change a=l*q at hl; nlinarith
    rw [e0,t_dyadic_block (l+1) m 1 (by omega),t_one,xor_not] at v0
    rw [e1,t_dyadic_block (l+1) m 2 (by omega),t_two,xor_not] at v1'
    have he := v0.symm.trans v1'
    cases c <;> contradiction
  · have hhalf : 2^(m-1)+1<2^m := by
      have hpos : 1<2^(m-1) := by have := index_lt_two_pow (m-1); omega
      have he : m=(m-1)+1 := by omega
      conv_rhs => rw [he,Nat.pow_succ]
      omega
    have e0 : a+q+1=(l+1)*q+(2^(m-1)+1) := by change a=l*q+2^(m-1) at hl; nlinarith
    rw [e0,t_dyadic_block (l+1) m (2^(m-1)+1) hhalf,half_plus_one hm,Bool.xor_false,hc1] at v0
    cases c <;> contradiction

theorem plus_not_penultimate {m a : ℕ} {c : Bool} (hm : 2≤m)
    (R : Run (a*2^m+(2^m-2)) (2^m+1) (2^m+2) c) : False := by
  let q := 2^m
  have hq : 4≤q := pow_ge_four hm
  have B : Block m (a+3) c := by
    intro r hr
    have v := plus_after R (k:=r+2) (by omega) (by omega) (by omega)
    have he : 2^m-2+(r+2)-2^m=r := by omega
    rw [he] at v
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using v
  have v0 := plus_before R (k:=0) (by omega) (by omega)
  have v1 := plus_before R (k:=1) (by omega) (by omega)
  simp only [Nat.add_zero] at v0
  have e1 : 2^m-2+1=2^m-1 := by omega
  rw [e1] at v1
  rcases block_cases hm B with ⟨l,hl,hc⟩ | ⟨l,hl,hc,hc1⟩
  · have hl1 : 1≤l := by
      by_contra hn
      have : l=0 := by omega
      subst l
      simp at hl
    have hls : l-1+1=l := by omega
    have ea0 : a=(l-1)*q+(q-3) := by
      change a+3=l*q at hl
      have : q-3+3=q := by omega
      nlinarith
    have ea1 : a+1=(l-1)*q+(q-2) := by
      change a+3=l*q at hl
      have : q-2+2=q := by omega
      nlinarith
    have he : t a=t (a+1) := by
      rw [ea1,ea0,t_dyadic_block (l-1) m (q-3) (by omega),t_dyadic_block (l-1) m (q-2) (by omega)]
      dsimp [q]
      rw [tail_three hm,tail_two hm]
    rw [v0,v1,tail_two hm] at he
    cases c <;> cases ht : t (2^m-1) <;> simp only [ht,Bool.xor_false,Bool.xor_true,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] at he <;> contradiction
  · have hhalf : 2≤2^(m-1) := by have := index_lt_two_pow (m-1); omega
    have hhalf_lt : 2^(m-1)<2^m := by
      have he : m=(m-1)+1 := by omega
      conv_rhs => rw [he,Nat.pow_succ]
      omega
    have ea : a+1=l*q+(2^(m-1)-2) := by change a+3=l*q+2^(m-1) at hl; omega
    rw [ea,t_dyadic_block l m (2^(m-1)-2) (by omega),half_tail_two hm,hc] at v1
    have he := xor_cancel _ _ _ v1
    cases c <;> contradiction

/-- Exact necessity for every starting index in the plus family. -/
theorem plus_necessary {m s : ℕ} {c : Bool} (hm : 2≤m)
    (R : Run s (2^m+1) (2^m+2) c) :
    ∃ l, Center l ∧ s+2^m+1=l*2^m*2^m ∧ c=t l := by
  let q := 2^m
  have hq : 4≤q := pow_ge_four hm
  let a := s/q
  let b := s%q
  have hs : s=a*q+b := by dsimp [a,b]; simpa [Nat.add_comm,Nat.mul_comm] using (Nat.mod_add_div s q).symm
  have hb : b<2^m := Nat.mod_lt s (by omega)
  have R' : Run (a*2^m+b) (2^m+1) (2^m+2) c := by
    change Run (a*q+b) (q+1) (q+2) c
    rw [←hs]
    exact R
  have hb1 : b=q-1 := by
    rcases plus_residue_options hm hb R' with hb0 | hb2 | hb1
    · rw [hb0] at R'
      exact False.elim (plus_not_zero hm R')
    · rw [hb2] at R'
      exact False.elim (plus_not_penultimate hm R')
    · exact hb1
  have hs1 : s=a*q+(q-1) := by omega
  have Rf : Run (a*2^m+(2^m-1)) (2^m+1) (2^m+2) c := by
    change Run (a*q+(q-1)) (q+1) (q+2) c
    rw [←hs1]
    exact R
  have B := plus_final_block hm Rf
  have left := plus_before Rf (k:=0) (by omega) (by omega)
  simp only [Nat.add_zero] at left
  have er : s+(q+1)*(q+1)=(a+q+3)*q+0 := by
    have : q-1+1=q := by omega
    nlinarith
  have right := run_at R (by omega : q+1<2^m+2) (pow_pos m) er
  simp only [t_zero,Bool.xor_false] at right
  rcases block_cases hm B with ⟨l,hl,hc⟩ | ⟨l,hl,hc,hc1⟩
  · have hl1 : 1≤l := by
      by_contra hn
      have : l=0 := by omega
      subst l
      simp at hl
    have hls : l-1+1=l := by omega
    have ea : a=(l-1)*q+(q-2) := by
      change a+2=l*q at hl
      have : q-2+2=q := by omega
      nlinarith
    rw [ea,t_dyadic_block (l-1) m (q-2) (by omega)] at left
    dsimp [q] at left
    rw [tail_two hm] at left
    have hleft : t (l-1)= !c := by
      cases h0 : t (l-1) <;> cases c <;> cases h1 : t (2^m-1) <;> simp_all only [Bool.xor_false,Bool.xor_true,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true]
    have eright : a+q+3=(l+1)*q+1 := by change a+2=l*q at hl; nlinarith
    rw [eright,t_dyadic_block (l+1) m 1 (by omega),t_one,xor_not] at right
    have hright : t (l+1)= !c := by simpa using congrArg Bool.not right
    refine ⟨l,⟨hl1,?_,?_⟩,?_,hc.symm⟩
    · simpa only [hc] using hleft
    · simpa only [hc] using hright
    · change s+q+1=l*q*q
      change a+2=l*q at hl
      have : q-1+1=q := by omega
      nlinarith
  · have hhalf : 2≤2^(m-1) := by have := index_lt_two_pow (m-1); omega
    have hhalf_lt : 2^(m-1)<2^m := by
      have he : m=(m-1)+1 := by omega
      conv_rhs => rw [he,Nat.pow_succ]
      omega
    have ea : a=l*q+(2^(m-1)-2) := by change a+2=l*q+2^(m-1) at hl; omega
    rw [ea,t_dyadic_block l m (2^(m-1)-2) (by omega),half_tail_two hm,hc] at left
    have he := xor_cancel _ _ _ left
    cases c <;> contradiction

end ThueMorseMAP

namespace ThueMorseMAP
open ThueMorseBits

theorem plus_witness {m l : ℕ} (hm : 2≤m) (hc : Center l) :
    Run ((l*2^m-2)*2^m+(2^m-1)) (2^m+1) (2^m+2) (t l) := by
  let q := 2^m
  have hq : 4≤q := pow_ge_four hm
  rcases hc with ⟨hl,hl0,hl1⟩
  have hlq : 2≤l*q := by nlinarith
  have hls : l-1+1=l := by omega
  have hlqs : l*q-2+2=l*q := by omega
  have hqm : q-1+1=q := by omega
  intro k hk
  change t ((l*q-2)*q+(q-1)+k*(q+1))=t l
  by_cases hk0 : k=0
  · subst k
    simp only [Nat.zero_mul,Nat.add_zero]
    rw [t_dyadic_block (l*q-2) m (q-1) (by omega)]
    have e : l*q-2=(l-1)*q+(q-2) := by
      have : q-2+2=q := by omega
      nlinarith
    rw [e,t_dyadic_block (l-1) m (q-2) (by omega)]
    dsimp [q]
    rw [tail_two hm,hl0]
    cases t l <;> cases t (2^m-1) <;> rfl
  by_cases hkmid : k≤q
  · let r := k-1
    have hr : r<q := by dsimp [r]; omega
    have hkr : k=r+1 := by dsimp [r]; omega
    have e : (l*q-2)*q+(q-1)+k*(q+1)=(l*q+r)*q+r := by nlinarith
    rw [e,t_dyadic_block (l*q+r) m r hr,t_dyadic_block l m r hr]
    cases t l <;> cases t r <;> rfl
  · have hk1 : k=q+1 := by omega
    subst k
    have e : (l*q-2)*q+(q-1)+(q+1)*(q+1)=((l+1)*q+1)*q := by nlinarith
    rw [e,t_mul_two_pow,t_dyadic_block (l+1) m 1 (by omega),t_one,xor_not,hl1,Bool.not_not]

theorem plus_classification {m s : ℕ} (hm : 2≤m) :
    Mono s (2^m+1) (2^m+2) ↔ ∃ l, Center l ∧ s+2^m+1=l*2^m*2^m := by
  constructor
  · rintro ⟨c,R⟩
    obtain ⟨l,hl,hs,_⟩ := plus_necessary hm R
    exact ⟨l,hl,hs⟩
  · rintro ⟨l,hl,hs⟩
    have hq := pow_ge_four hm
    have hlq : 2≤l*2^m := by have := hl.1; nlinarith
    have hsub := Nat.sub_add_cancel hlq
    have hqsub : 2^m-1+1=2^m := by omega
    have he : s=(l*2^m-2)*2^m+(2^m-1) := by nlinarith
    rw [he]
    exact ⟨t l,plus_witness hm hl⟩

theorem plus_upper {m : ℕ} (hm : 2≤m) (s : ℕ) :
    ¬ Mono s (2^m+1) (2^m+2+1) := by
  rintro ⟨c,R⟩
  have R0 : Run s (2^m+1) (2^m+2) c := fun k hk => R k (by omega)
  have R1 := run_shift R
  obtain ⟨l,_,e0,_⟩ := plus_necessary hm R0
  obtain ⟨j,_,e1,_⟩ := plus_necessary hm R1
  have hq := pow_ge_four hm
  have he : l*2^m*2^m+(2^m+1)=j*2^m*2^m := by omega
  have hmod := congrArg (fun x => x%(2^m)) he
  have hrem1 : 1%(2^m)=1 := Nat.mod_eq_of_lt (by omega)
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mod,Nat.mul_zero,Nat.zero_add,Nat.add_zero,Nat.mod_mod,hrem1] at hmod
  omega

theorem plus_first_maximum {m : ℕ} (hm : 2≤m) :
    FirstMaximum (2^m+1) (2^m+2) (3*2^m*2^m-2^m-1) := by
  have hq := pow_ge_four hm
  have hmul : 2^m+1≤3*2^m*2^m := by nlinarith
  have hsub : 3*2^m*2^m-2^m-1+2^m+1=3*2^m*2^m := by omega
  constructor
  · apply (plus_classification hm).mpr
    exact ⟨3,center_three,hsub⟩
  constructor
  · exact plus_upper hm
  · intro a ha H
    obtain ⟨l,hl,he⟩ := (plus_classification hm).mp H
    have hl3 := center_ge_three hl
    have hmul3 := Nat.mul_le_mul_right (2^m*2^m) hl3
    nlinarith

#print axioms plus_first_maximum
end ThueMorseMAP
