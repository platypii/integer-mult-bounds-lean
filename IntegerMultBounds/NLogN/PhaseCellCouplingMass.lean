module

public import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.PhaseCellCouplingOffsets

/-! The executed offset list has the original matrix's row mass, including aliases. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open SchurDominance

variable {s t : ℕ} [NeZero s]

theorem couplingOffsets_mass_eq_row (p u : ℕ) (i : ZMod s) :
    (((couplingOffsets (PhaseCellBand.width p u)).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u) i.val (i.val+δ) : ℝ)|)).sum =
      ∑ j, realMatrix s t p u i j := by
  have hnonneg (δ : ℤ) : 0 ≤ (PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u)
      i.val (i.val+δ) : ℝ) := by
    exact_mod_cast entry_nonneg (2^15*p) s t u (PhaseCellBand.width p u) i.val (i.val+δ)
  simp_rw [abs_of_nonneg (hnonneg _)]
  rw [List.map_reverse,List.sum_reverse]
  have hc := couple_eq_offsetList (s := s) (t := t) p u Finset.univ (fun _ => 1) i
  simpa [couple] using hc.symm

theorem matrix_row_sum_le_two [NeZero t] (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p) (i : ZMod s) :
    ∑ j, realMatrix s t p u i j ≤ 2 := by
  have hnorm := rounded_sub_one s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hone : ‖(fun _ : ZMod s => (1 : ℂ))‖ ≤ 1 := by simp
  have hv := (PhaseCellOperator.rounded s t p u-1).le_of_opNorm_le_of_le hnorm hone
  have hi := (norm_le_pi_norm ((PhaseCellOperator.rounded s t p u-1) (fun _ => 1)) i).trans hv
  simp only [sub_apply,Pi.sub_apply,ContinuousLinearMap.one_def,ContinuousLinearMap.id_apply,mul_one] at hi
  rw [← row_sum s t p u i,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hi
  have hle := le_abs_self ((∑ j, realMatrix s t p u i j)-1)
  have hmargin : 0 ≤ 1/(8*(p : ℝ)) := by positivity
  linarith

theorem couplingOffsets_mass_le_two (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p) (i : ℕ) (hi : i < s) :
    (((couplingOffsets (PhaseCellBand.width p u)).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u) i (i+δ) : ℝ)|)).sum ≤ 2 := by
  let : NeZero t := ⟨by omega⟩
  have hmass := couplingOffsets_mass_eq_row (t := t) p u (i : ZMod s)
  have hsum := matrix_row_sum_le_two hst hα p u hp hwidth hαu hθ hgap hbudget (i : ZMod s)
  simpa [ZMod.val_natCast,Nat.mod_eq_of_lt hi,← hmass] using hsum

end IntegerMultBounds.NLogN.PhaseCellMatrix
