module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvDecode
public import IntegerMultBounds.NLogN.PhaseCellHaloSchurStability

/-! The computed Schur matrix/solve contracts imply recovery's allocated boundary tolerance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open scoped BigOperators
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem boundaryTable_row_budget {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (S Sh : Matrix ι ι ℝ) (p target rhsExp : ℕ)
    (hentry : ∀ i ∈ B, ∀ j ∈ B, |Sh i j-S i j| ≤
      1/(2 : ℝ)^boundaryTableBits p target rhsExp B.card) :
    ∀ i ∈ B, ∑ j ∈ B, |Sh i j-S i j| ≤ 1/(2 : ℝ)^boundaryErrorBits p target rhsExp := by
  intro i hi
  calc
    _ ≤ ∑ j ∈ B, 1/(2 : ℝ)^boundaryTableBits p target rhsExp B.card := Finset.sum_le_sum (fun j hj => hentry i hi j hj)
    _ = (B.card : ℝ)*(1/(2 : ℝ)^boundaryTableBits p target rhsExp B.card) := by simp
    _ ≤ _ := boundaryTable_error_budget p target rhsExp B.card

theorem haloBoundary_tolerance {s t p u a b q target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) (R c) c)
    (Sh : Matrix (ZMod s) (ZMod s) ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδbits : δ ≤ 1/(2 : ℝ)^boundaryErrorBits p (recoveryTarget p target) rhsExp)
    (hShentry : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ∀ j ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
        |Sh i j-(SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j| ≤
          1/(2 : ℝ)^boundaryTableBits p (recoveryTarget p target) rhsExp
            (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (rhs x : ZMod s → ℝ) (C X : ZMod s → GaussianInt)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x rhs)
    (hC : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (hrE : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      8*p*|(value q (C i)).re-SchurDominance.residual (realMatrix s t p u)
        (haloInterior s t (PhaseCellBand.width p u) a b) R rhs i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2))
    (hX : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |(∑ j ∈ haloBoundary s t (PhaseCellBand.width p u) a b, Sh i j*(value q (X j)).re)-(value q (C i)).re| ≤ δ) :
    PhaseCellInterface.ErrorOn (haloBoundary s t (PhaseCellBand.width p u) a b)
      (fun i => (value q (X i)).re) x (1/(2 : ℝ)^recoveryTarget p target) := by
  let εA := 1/(2 : ℝ)^boundaryErrorBits p (recoveryTarget p target) rhsExp
  have hεA : 0 ≤ εA := by dsimp [εA]; positivity
  have hSh := boundaryTable_row_budget (haloBoundary s t (PhaseCellBand.width p u) a b)
    (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
      (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 Sh p (recoveryTarget p target) rhsExp hShentry
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  let E := (1/(2 : ℝ)^(recoveryTarget p target+2))/(8*p)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEbudget : 8*p*E ≤ 1/(2 : ℝ)^(recoveryTarget p target+2) := by
    dsimp [E]
    rw [mul_div_cancel₀ _ (show (8*(p : ℝ)) ≠ 0 by positivity)]
  obtain ⟨hsmall,hbudgetError⟩ := boundary_error_budget p (recoveryTarget p target) rhsExp
    (by omega) hεA hδ le_rfl hδbits hEbudget
  have hres : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |(value q (C i)).re-SchurDominance.residual (realMatrix s t p u)
        (haloInterior s t (PhaseCellBand.width p u) a b) R rhs i| ≤ E := by
    intro i hi
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8*p)).mpr
    simpa only [mul_comm] using hrE i hi
  have herror := (halo_computed_schur_error hst hα p u a b hp hwidth hαu hθ hgap hbudget R hR
    Sh εA hεA hsmall hSh rhs x (fun i => (value q (C i)).re) (fun i => (value q (X i)).re) hx
    ((2 : ℝ)^rhsExp) δ E (by positivity) hδ hE
    (fun i hi => (Complex.abs_re_le_norm _).trans (hC i hi)) hres hX).2
  intro i hi
  simpa only [Real.norm_eq_abs] using (herror i hi).trans hbudgetError

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
