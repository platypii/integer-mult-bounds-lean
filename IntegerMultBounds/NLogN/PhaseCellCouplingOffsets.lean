module

public import IntegerMultBounds.NLogN.PhaseCellMatrix
public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! Coupling rows enumerate retained lattice offsets, rather than deduplicating
wrapped columns. Distinct offsets reaching the same residue all contribute. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open PhaseCellRow SchurDominance

def couplingOffsets (band : ℕ) : List ℤ :=
  0::((List.range band).map (fun n : ℕ => (n : ℤ)+1)++
    (List.range band).map (fun n : ℕ => -((n : ℤ)+1)))

@[simp] theorem couplingOffsets_length (band : ℕ) :
    (couplingOffsets band).length = 2*band+1 := by simp [couplingOffsets]; omega

theorem couplingOffsets_sum {E : Type*} [AddCommMonoid E] (f : ℤ → E) (band : ℕ) :
    ((couplingOffsets band).map f).sum = window f band := by
  have hsum (g : ℕ → E) : ((List.range band).map g).sum = ∑ n ∈ Finset.range band, g n := by
    rw [← List.sum_toFinset _ (List.nodup_range (n := band))]
    congr
    ext n
    simp
  simp only [couplingOffsets,List.map_cons,List.map_append,List.sum_cons,List.sum_append,
    List.map_map,Function.comp_def,hsum,window]
  ac_rfl

theorem couple_eq_offsetWindow {s t : ℕ} [NeZero s] (p u : ℕ)
    (T : Finset (ZMod s)) (x : ZMod s → ℝ) (i : ZMod s) :
    couple (realMatrix s t p u) T x i =
      window (fun δ : ℤ => if i+(δ : ZMod s) ∈ T then
        (PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u)
          (i.val : ℤ) (i.val+δ) : ℝ)*x (i+(δ : ZMod s)) else 0) (PhaseCellBand.width p u) := by
  simp only [couple,realMatrix,matrix,window,Rat.cast_add,Rat.cast_sum,
    add_mul,Finset.sum_add_distrib,Finset.sum_mul]
  rw [Finset.sum_comm (s := T) (t := Finset.range _),
    Finset.sum_comm (s := T) (t := Finset.range _)]
  congr 2
  all_goals simp [apply_ite,ite_mul]
  all_goals by_cases hi : i ∈ T <;> simp [hi]

/-- This list is the exact original principal-system coupling, including aliases. -/
theorem couple_eq_offsetList {s t : ℕ} [NeZero s] (p u : ℕ)
    (T : Finset (ZMod s)) (x : ZMod s → ℝ) (i : ZMod s) :
    couple (realMatrix s t p u) T x i =
      ((couplingOffsets (PhaseCellBand.width p u)).map (fun δ : ℤ =>
        if i+(δ : ZMod s) ∈ T then
          (PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u)
            (i.val : ℤ) (i.val+δ) : ℝ)*x (i+(δ : ZMod s)) else 0)).sum := by
  rw [couplingOffsets_sum]
  exact couple_eq_offsetWindow p u T x i

end IntegerMultBounds.NLogN.PhaseCellMatrix
