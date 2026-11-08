module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundedDiagonalAccuracy

/-! Execute D' on actual rounded recovery words, deriving multiplier fits. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
variable {s t α p q W c n target T Q A : ℕ} [NeZero s] [NeZero t]
  {P U : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_roundedDiagonal_runs_within
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o)
    (ρ : RsbR → List (Fin (A+4))) (hr : RsbReady ρ W p)
    (hp : 13 ≤ p) (hpq : p ≤ q) (hW : 2*p+13 ≤ W) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (active : Finset (ZMod s)) (hfit : c+n ≤ s)
    (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+n)
    (hcover : ∀ i : ZMod s, c ≤ i.val → i.val < c+n → i ∈ active)
    (D : ZMod s → GaussianInt) (z : ZMod s → ℂ)
    (hmag : ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (hscale : ∀ i ∈ active, ‖((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i‖ ≤ (3/2 : ℝ))
    (oldTail : List (Fin (A+4)))
    (herror : PhaseCellInterface.ErrorOn active
      (packedIntervalRead q (2*q+8) c (cstream A (2*q+8) (packedInterval c n D)++oldTail)) z (1/(2 : ℝ)^target))
    (hx : ρ x = cstream A W (packedInterval c n
      (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))))
    (hy : ρ y = cstream A W (packedInterval c n (diagonalField s t α p)))
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg x y o)) ≤ C) :
    let G := fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)
    RsbRunsWithin (body := body) (rg := rg) (ι := ι)
      (cmulStream (rsbCr rg x y o) (rmulOne ι hι hT hQ (rsbCr rg x y o))) ρ
      (Function.update ρ o (cstream A W (packedInterval c n (diagonalProduct s t α p G))++ρ o))
      (n*(rmulCost W+6*W+2)+8) (realWeightWorkspace C W n) ∧
    PhaseCellInterface.ErrorOn active
      (packedIntervalRead p W c (cstream A W (packedInterval c n (diagonalProduct s t α p G))++ρ o))
      (fun i => (dPrime s t (α : ℝ) i : ℂ)*(((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i))
      (8/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)) := by
  dsimp only
  have hA4 : 4 ≤ A := by omega
  obtain ⟨hfits,_,haccuracy⟩ := roundedDiagonal_accuracy (t := t) (α := α) hA4 hp hpq hW hα hαp
    active hfit hactive D z hmag hscale oldTail (ρ o) herror
  refine ⟨?_,haccuracy⟩
  exact rsb_diagonalInterval_runs_within (body := body) hrg hdisj hι hT hQ hA hfree ρ hr
    (by omega) hp hα hαp _ hfit (packedInterval_fits_of_active _ active hfit hcover hfits) hx hy C hpush

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
