import G3FixedDegreeResultants
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

noncomputable section
namespace GProgram.G3.AllResidue.SliceThree
open scoped BigOperators
open Polynomial
open GProgram.G3.AllResidue

def pCoeffTable (i : Fin 5) (j : Fin 6) : ℝ := match i.val,j.val with
  | 0,0 => (10460353160 : ℝ)/(21 : ℝ)
  | 0,1 => (150719755845189200 : ℝ)/(21 : ℝ)
  | 0,2 => (8970395826433850912480 : ℝ)/(21 : ℝ)
  | 0,3 => (6326337373067217933119680 : ℝ)/(21 : ℝ)
  | 0,4 => (-99660936110756676504442880 : ℝ)/(21 : ℝ)
  | 0,5 => (-958599085887796467208540160 : ℝ)/(3 : ℝ)
  | 1,0 => (10460353020 : ℝ)/(7 : ℝ)
  | 1,1 => (150718289378526168 : ℝ)/(7 : ℝ)
  | 1,2 => (8949294927567288717072 : ℝ)/(7 : ℝ)
  | 1,3 => (5070296178147498989706912 : ℝ)/(7 : ℝ)
  | 1,4 => (-996424243799855414081860608 : ℝ)/(7 : ℝ)
  | 1,5 => (-287579725766338940162562048 : ℝ)
  | 2,0 => (20920701308 : ℝ)/(7 : ℝ)
  | 2,1 => (301387012187385176 : ℝ)/(7 : ℝ)
  | 2,2 => (17185416588892216476656 : ℝ)/(7 : ℝ)
  | 2,3 => (-31779575110091066982754784 : ℝ)/(7 : ℝ)
  | 2,4 => (-902402089627263848871028352 : ℝ)/(7 : ℝ)
  | 2,5 => (-239649771471949116802135040 : ℝ)
  | 3,0 => (104602292012 : ℝ)/(21 : ℝ)
  | 3,1 => (1494213242502911288 : ℝ)/(21 : ℝ)
  | 3,2 => (-96361093906567860489808 : ℝ)/(21 : ℝ)
  | 3,3 => (-73672405942793792253193568 : ℝ)/(21 : ℝ)
  | 3,4 => (-1992262595890265246054249600 : ℝ)/(21 : ℝ)
  | 3,5 => (-527229497238288056964697088 : ℝ)/(3 : ℝ)
  | 4,0 => (52201323668 : ℝ)/(7 : ℝ)
  | 4,1 => (-297067401683952952 : ℝ)/(7 : ℝ)
  | 4,2 => (-17950186536836529795664 : ℝ)/(7 : ℝ)
  | 4,3 => (-13406606232573660190501664 : ℝ)/(7 : ℝ)
  | 4,4 => (-362251094156268786477612032 : ℝ)/(7 : ℝ)
  | 4,5 => (-95859908588779646720854016 : ℝ)
  | _,_ => 0

def qCoeffTable (i : Fin 5) (j : Fin 5) : ℝ := match i.val,j.val with
  | 0,0 => (-3486784400 : ℝ)
  | 0,1 => (-50240058278555200 : ℝ)
  | 0,2 => (-2992141555917980980800 : ℝ)
  | 0,3 => (-2228464795136908381081600 : ℝ)
  | 0,4 => (-55918279999429989863321600 : ℝ)
  | 1,0 => (-10460353176 : ℝ)
  | 1,1 => (-150719923441380384 : ℝ)
  | 1,2 => (-8972807369498139140064 : ℝ)
  | 1,3 => (-6470054227759271716030464 : ℝ)
  | 1,4 => (-12904218431799771040892928 : ℝ)
  | 2,0 => (-20920704948 : ℝ)
  | 2,1 => (-301425140318094936 : ℝ)
  | 2,2 => (-17734013467997701198896 : ℝ)
  | 2,3 => (-496331734299553010285856 : ℝ)
  | 2,4 => (-921729826127903029256448 : ℝ)
  | 3,0 => (-34867647180 : ℝ)
  | 3,1 => (-500338951768253160 : ℝ)
  | 3,2 => (-378237031976438490960 : ℝ)
  | 3,3 => (-10224389446525918740960 : ℝ)
  | 3,4 => (-18939833476202347188480 : ℝ)
  | 4,0 => (-52230021480 : ℝ)
  | 4,1 => (-3123564204589920 : ℝ)
  | 4,2 => (-2332630573832351520 : ℝ)
  | 4,3 => (-63028201529155000320 : ℝ)
  | 4,4 => (-116750868440936970240 : ℝ)
  | _,_ => 0

def modelP (x : Fin 5 → ℝ) : Polynomial ℝ :=
  ∑ k : Fin 6, C (∑ i : Fin 5, pCoeffTable i k*x i)*X^k.val

def modelQ (x : Fin 5 → ℝ) : Polynomial ℝ :=
  ∑ k : Fin 5, C (∑ i : Fin 5, qCoeffTable i k*x i)*X^k.val

theorem erase_univ_0 : (Finset.univ : Finset (Fin 6)).erase 0 = {1, 2, 3, 4, 5} := by decide
theorem erase_univ_1 : (Finset.univ : Finset (Fin 6)).erase 1 = {0, 2, 3, 4, 5} := by decide
theorem erase_univ_2 : (Finset.univ : Finset (Fin 6)).erase 2 = {0, 1, 3, 4, 5} := by decide
theorem erase_univ_3 : (Finset.univ : Finset (Fin 6)).erase 3 = {0, 1, 2, 4, 5} := by decide
theorem erase_univ_4 : (Finset.univ : Finset (Fin 6)).erase 4 = {0, 1, 2, 3, 5} := by decide
theorem erase_univ_5 : (Finset.univ : Finset (Fin 6)).erase 5 = {0, 1, 2, 3, 4} := by decide

theorem modelP_is_actual_source (x : Fin 5 → ℝ) :
    modelP x = criticalProbabilityPolynomial (fullWeight x) capSevenExponent 3 := by
  apply Polynomial.funext
  intro p
  rw [critical_probability_eval]
  simp only [modelP, Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  norm_num [Fin.sum_univ_succ,pCoeffTable,pCriticalNumerator,
    fullWeight,capSevenExponent,bernoulliFactor,
    erase_univ_0,erase_univ_1,erase_univ_2,erase_univ_3,erase_univ_4,erase_univ_5]
  ring

theorem modelQ_is_actual_source_quotient (x : Fin 5 → ℝ) :
    (1-X)*modelQ x = sourceQProbabilityPolynomial (fullWeight x) capSevenExponent 3 := by
  apply Polynomial.funext
  intro p
  rw [source_q_probability_eval]
  simp only [modelQ, Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,
    Polynomial.eval_X,Polynomial.eval_finsetSum,Polynomial.eval_C,Polynomial.eval_pow]
  norm_num [Fin.sum_univ_succ,qCoeffTable,qCriticalNumerator,
    fullWeight,capSevenExponent,bernoulliFactor,
    erase_univ_0,erase_univ_1,erase_univ_2,erase_univ_3,erase_univ_4,erase_univ_5]
  ring

#print axioms modelP_is_actual_source
#print axioms modelQ_is_actual_source_quotient
end GProgram.G3.AllResidue.SliceThree
