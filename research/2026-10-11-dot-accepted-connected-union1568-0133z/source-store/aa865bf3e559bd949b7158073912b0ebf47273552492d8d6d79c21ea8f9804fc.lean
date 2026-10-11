import ThueMorseMAP.Blocks
namespace ThueMorseMAP
open ThueMorseBits

/-- A wrap cannot have two progression terms on each exterior side. -/
theorem minus_wrap_impossible {m s L k H : ℕ} {c : Bool}
    (hm : 2≤m) (hp : m%2=0) (R : Run s (2^m-1) L c)
    (hk : 2≤k) (hkL : k+3<L) (hw : s+k*(2^m-1)=H*2^m) : False := by
  let q := 2^m
  have hq : 4≤q := pow_ge_four hm
  have hqm : q-1+1=q := by omega
  change s+k*(q-1)=H*q at hw
  have hH : 2≤H := by
    by_contra hn
    interval_cases H <;> nlinarith
  have hk2 : k-2+2=k := by omega
  have hH2 : H-2+2=H := by omega
  have hk1 : k-1+1=k := by omega
  have hH1 : H-1+1=H := by omega
  have e0 : s+(k-2)*(q-1)=(H-2)*q+2 := by change s+k*(q-1)=H*q at hw; nlinarith
  have e1 : s+(k-1)*(q-1)=(H-1)*q+1 := by change s+k*(q-1)=H*q at hw; nlinarith
  have e2 : s+(k+2)*(q-1)=(H+1)*q+(q-2) := by
    change s+k*(q-1)=H*q at hw
    have : q-2+2=q := by omega
    nlinarith
  have e3 : s+(k+3)*(q-1)=(H+2)*q+(q-3) := by
    change s+k*(q-1)=H*q at hw
    have : q-3+3=q := by omega
    nlinarith
  have v0 := run_at R (by omega : k-2<L) (by omega : 2<2^m) e0
  have v1 := run_at R (by omega : k-1<L) (by omega : 1<2^m) e1
  have v2 := run_at R (by omega : k+2<L) (by omega : q-2<2^m) e2
  have v3 := run_at R (by omega : k+3<L) (by omega : q-3<2^m) e3
  have htail : t (2^m-1)=false := by rw [tail_one]; simp [hp]
  simp only [t_one,t_two,xor_not] at v0 v1
  dsimp [q] at v2 v3
  rw [tail_two hm,htail,Bool.not_false,xor_not] at v2
  rw [tail_three hm,htail,Bool.not_false,xor_not] at v3
  have he0 : t (H-2)=t (H-2+1) := by
    have : H-2+1=H-1 := by omega
    rw [this,v0,v1]
  have he1 : t (H+1)=t (H+1+1) := by simpa [Nat.add_assoc] using v2.trans v3.symm
  have ho0 := equal_adjacent_odd he0
  have ho1 := equal_adjacent_odd he1
  omega

/-- The local wrap obstruction fixes the residue of every full run. -/
theorem even_minus_residue {m a b : ℕ} {c : Bool}
    (hm : 2≤m) (hp : m%2=0) (hb : b<2^m)
    (R : Run (a*2^m+b) (2^m-1) (2^m+4) c) : b=1 := by
  let q := 2^m
  have hq : 4≤q := pow_ge_four hm
  have hqm : q-1+1=q := by omega
  by_contra hn
  by_cases hb0 : b=0
  · have hH : a+q-1+1=a+q := by omega
    apply minus_wrap_impossible hm hp R (k:=q) (H:=a+q-1) (by omega) (by omega)
    change a*q+b+q*(q-1)=(a+q-1)*q
    subst b
    nlinarith
  · apply minus_wrap_impossible hm hp R (k:=b) (H:=a+b) (by omega) (by omega)
    change a*q+b+b*(q-1)=(a+b)*q
    nlinarith

/-- Necessary scale-free characterization, over all starting indices. -/
theorem even_minus_necessary {m s : ℕ} {c : Bool}
    (hm : 2≤m) (hp : m%2=0) (R : Run s (2^m-1) (2^m+4) c) :
    ∃ l, Center l ∧ s+2^m=l*2^m*2^m+1 ∧ c=t l := by
  let q := 2^m
  have hq : 4≤q := pow_ge_four hm
  let a := s/q
  let b := s%q
  have hs : s=a*q+b := by dsimp [a,b]; simpa [Nat.add_comm,Nat.mul_comm] using (Nat.mod_add_div s q).symm
  have hb : b<2^m := Nat.mod_lt s (by omega)
  have R' : Run (a*2^m+b) (2^m-1) (2^m+4) c := by
    change Run (a*q+b) (q-1) (q+4) c
    rw [←hs]
    exact R
  have hb1 := even_minus_residue hm hp hb R'
  have hs1 : s=a*q+1 := by omega
  have htail : t (q-1)=false := by dsimp [q]; rw [tail_one]; simp [hp]
  have hqm : q-1+1=q := by omega
  have B : Block m (a+1) c := by
    intro r hr
    have hsub : q-1-r+r+1=q := by omega
    have e : s+(r+2)*(q-1)=(a+1+r)*q+(q-1-r) := by nlinarith
    have v := run_at R (by omega : r+2<2^m+4) (by omega : q-1-r<2^m) e
    dsimp [q] at v
    rw [complement m r hr] at v
    simpa [hp] using v
  have eleft : s+0*(q-1)=a*q+1 := by omega
  have left := run_at R (by omega : 0<2^m+4) (by omega : 1<2^m) eleft
  simp only [t_one,xor_not] at left
  have esub : q-2+2=q := by omega
  have eright : s+(q+3)*(q-1)=(a+q+1)*q+(q-2) := by nlinarith
  have right := run_at R (by omega : q+3<2^m+4) (by omega : q-2<2^m) eright
  have htail2 : t (q-2)=true := by dsimp [q]; rw [tail_two hm]; change (!t (q-1))=true; rw [htail]; rfl
  rw [htail2,xor_not] at right
  rcases block_cases hm B with ⟨l,hl,hc⟩ | ⟨l,hl,hc,hc1⟩
  · have hl1 : 1≤l := by
      by_contra hn
      have hl0 : l=0 := by omega
      subst l
      simp at hl
    have hls : l-1+1=l := by omega
    have ea : a=(l-1)*q+(q-1) := by change a+1=l*q at hl; nlinarith
    rw [ea,t_dyadic_block (l-1) m (q-1) (by omega),htail,Bool.xor_false] at left
    have er : a+q+1=(l+1)*q := by change a+1=l*q at hl; nlinarith
    rw [er,t_mul_two_pow] at right
    refine ⟨l,⟨hl1,?_,?_⟩,?_,hc.symm⟩
    · simpa only [hc] using left
    · simpa only [hc] using right
    · change s+q=l*q*q+1
      change a+1=l*q at hl
      nlinarith
  · have hhalf : 0<2^(m-1) := pow_pos (m-1)
    have hhalf_lt : 2^(m-1)<2^m := by
      have he : m=(m-1)+1 := by omega
      conv_rhs => rw [he,Nat.pow_succ]
      omega
    have ea : a=l*q+(2^(m-1)-1) := by change a+1=l*q+2^(m-1) at hl; omega
    rw [ea,t_dyadic_block l m (2^(m-1)-1) (by omega),half_tail_one hm] at left
    change Bool.xor (t l) (!(t (q-1)))= !c at left
    rw [htail,Bool.not_false,xor_not,hc,Bool.not_not] at left
    cases c <;> contradiction

end ThueMorseMAP

namespace ThueMorseMAP
open ThueMorseBits

theorem even_minus_witness {m l : ℕ} (hm : 2≤m) (hp : m%2=0) (hc : Center l) :
    Run ((l*2^m-1)*2^m+1) (2^m-1) (2^m+4) (t l) := by
  let q := 2^m
  have hq : 4≤q := pow_ge_four hm
  rcases hc with ⟨hl,hl0,hl1⟩
  have hlq : 1≤l*q := by nlinarith
  have hls : l-1+1=l := by omega
  have hlqs : l*q-1+1=l*q := by omega
  have hqm : q-1+1=q := by omega
  have htail : t (q-1)=false := by dsimp [q]; rw [tail_one]; simp [hp]
  have htail2 : t (q-2)=true := by
    dsimp [q]
    rw [tail_two hm]
    change (!t (q-1))=true
    rw [htail]
    rfl
  intro k hk
  change t ((l*q-1)*q+1+k*(q-1))=t l
  by_cases hk0 : k=0
  · subst k
    simp only [Nat.zero_mul,Nat.add_zero]
    rw [t_dyadic_block (l*q-1) m 1 (by omega),t_one,xor_not]
    have e : l*q-1=(l-1)*q+(q-1) := by nlinarith
    rw [e,t_dyadic_block (l-1) m (q-1) (by omega),htail,Bool.xor_false,hl0,Bool.not_not]
  by_cases hk1 : k=1
  · subst k
    have e : (l*q-1)*q+1+1*(q-1)=(l*q)*q := by nlinarith
    rw [e,t_mul_two_pow,t_mul_two_pow]
  by_cases hkmid : k≤q+1
  · let r := k-2
    have hr : r<q := by dsimp [r]; omega
    have hkr : k=r+2 := by dsimp [r]; omega
    have hrs : q-1-r+r+1=q := by omega
    have e : (l*q-1)*q+1+k*(q-1)=(l*q+r)*q+(q-1-r) := by nlinarith
    rw [e,t_dyadic_block (l*q+r) m (q-1-r) (by omega),t_dyadic_block l m r hr]
    have ht : t (q-1-r)=t r := by dsimp [q]; simpa [hp] using complement m r hr
    rw [ht]
    cases t l <;> cases t r <;> rfl
  by_cases hk2 : k=q+2
  · subst k
    have e : (l*q-1)*q+1+(q+2)*(q-1)=(l*q+(q-1))*q+(q-1) := by nlinarith
    rw [e,t_dyadic_block (l*q+(q-1)) m (q-1) (by omega),t_dyadic_block l m (q-1) (by omega),htail]
    simp
  · have hk3 : k=q+3 := by omega
    subst k
    have hsub : q-2+2=q := by omega
    have e : (l*q-1)*q+1+(q+3)*(q-1)=((l+1)*q)*q+(q-2) := by nlinarith
    rw [e,t_dyadic_block ((l+1)*q) m (q-2) (by omega),t_mul_two_pow,htail2,xor_not,hl1,Bool.not_not]

/-- Exact classification, stated without truncated subtraction in the index equation. -/
theorem even_minus_classification {m s : ℕ} (hm : 2≤m) (hp : m%2=0) :
    Mono s (2^m-1) (2^m+4) ↔ ∃ l, Center l ∧ s+2^m=l*2^m*2^m+1 := by
  constructor
  · rintro ⟨c,R⟩
    obtain ⟨l,hl,hs,_⟩ := even_minus_necessary hm hp R
    exact ⟨l,hl,hs⟩
  · rintro ⟨l,hl,hs⟩
    have hq := pow_ge_four hm
    have hlq : 1≤l*2^m := by have := hl.1; nlinarith
    have hsub := Nat.sub_add_cancel hlq
    have he : s=(l*2^m-1)*2^m+1 := by nlinarith
    rw [he]
    exact ⟨t l,even_minus_witness hm hp hl⟩

theorem even_minus_upper {m : ℕ} (hm : 2≤m) (hp : m%2=0) (s : ℕ) :
    ¬ Mono s (2^m-1) (2^m+4+1) := by
  rintro ⟨c,R⟩
  have R0 : Run s (2^m-1) (2^m+4) c := fun k hk => R k (by omega)
  have R1 := run_shift R
  obtain ⟨l,_,e0,_⟩ := even_minus_necessary hm hp R0
  obtain ⟨j,_,e1,_⟩ := even_minus_necessary hm hp R1
  have hq := pow_ge_four hm
  have he : l*2^m*2^m+(2^m-1)=j*2^m*2^m := by omega
  have hmod := congrArg (fun x => x%(2^m)) he
  have hrem : (2^m-1)%(2^m)=2^m-1 := Nat.mod_eq_of_lt (by omega)
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mod,Nat.mul_zero,Nat.zero_add,Nat.add_zero,Nat.mod_mod,hrem] at hmod
  omega

theorem even_minus_first_maximum {m : ℕ} (hm : 2≤m) (hp : m%2=0) :
    FirstMaximum (2^m-1) (2^m+4) (3*2^m*2^m-2^m+1) := by
  have hq := pow_ge_four hm
  have hmul : 2^m≤3*2^m*2^m := by nlinarith
  have hsub := Nat.sub_add_cancel hmul
  constructor
  · apply (even_minus_classification hm hp).mpr
    exact ⟨3,center_three,by omega⟩
  constructor
  · exact even_minus_upper hm hp
  · intro a ha H
    obtain ⟨l,hl,he⟩ := (even_minus_classification hm hp).mp H
    have hl3 := center_ge_three hl
    have hmul3 := Nat.mul_le_mul_right (2^m*2^m) hl3
    nlinarith

#print axioms even_minus_first_maximum
end ThueMorseMAP
