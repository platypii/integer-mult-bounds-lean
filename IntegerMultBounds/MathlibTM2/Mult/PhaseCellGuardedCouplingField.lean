module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingRowValue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingFieldError
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealCouplingField

/-! State coupling accuracy directly on the computed integer field after exact decoding. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem guardedCouplingRowField_error {A s t p u q w rhsExp inputExp countExp a b : ℕ}
    [NeZero s] {α d : ℝ} (boundary : Bool) (hA : 96 ≤ A) (hp : 0 < p) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (C B : ZMod s → GaussianInt) (x b₀ : ZMod s → ℝ) (K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*PhaseCellBand.width p u+1 ≤ 2^countExp)
    (hB : ∀ i, ‖value q (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ (if boundary then haloBoundary s t (PhaseCellBand.width p u) a b
        else haloInterior s t (PhaseCellBand.width p u) a b), ‖value q (C i)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ i ∈ (if boundary then haloBoundary s t (PhaseCellBand.width p u) a b
        else haloInterior s t (PhaseCellBand.width p u) a b), |(value q (C i)).re-x i| ≤ ε)
    (hmass : ∀ i < s, (((couplingOffsets (PhaseCellBand.width p u)).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u) i (i+δ) : ℝ)|)).sum ≤ K)
    (hBError : ∀ i, |(value q (B i)).re-b₀ i| ≤ rhsError) (hbS : b ≤ s) :
    ∀ i, (boundary = true ∨ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b) → |(value q (guardedCouplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b boundary C B i)).re-
      (b₀ i-SchurDominance.couple (realMatrix s t p u)
        (if boundary then haloBoundary s t (PhaseCellBand.width p u) a b
          else haloInterior s t (PhaseCellBand.width p u) a b) x i)| ≤
      (2*PhaseCellBand.width p u+1)*(2/(2 : ℝ)^q)+rhsError+
        (2*PhaseCellBand.width p u+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  intro i hobserved
  rw [guardedCouplingRowField_eq hst (2^15*p) q u (PhaseCellBand.width p u) a b boundary hbS C B i hobserved]
  exact couplingRowField_error boundary hA hp hst hαu hθ hgap hbudget hw C B x b₀ K ε rhsError
    hε hcount hB hC hx hmass hBError i

theorem guardedCouplingRowField_realPart {s : ℕ} [NeZero s] (P q t u band a b : ℕ)
    (boundary : Bool) (C B : ZMod s → GaussianInt) (i : ZMod s) :
    realPartWord (guardedCouplingRowField P q t u band a b boundary C B i) =
      guardedCouplingRowField P q t u band a b boundary
        (fun j => realPartWord (C j)) (fun j => realPartWord (B j)) i := by
  unfold guardedCouplingRowField guardedCouplingRowWord
  split
  · rfl
  · exact couplingRowField_realPart P q t u band a b boundary C B i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
