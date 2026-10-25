module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedAccuracy
public import IntegerMultBounds.NLogN.PhaseCellGeneratedInterval

/-! # Published accuracy on a computed ambient interior interval -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- One anchor in the ambient interior determines the interval and mask; no
fit, same-cell, coverage or maximality oracle is supplied. -/
theorem generatedCell_accuracy {A s t p u l j rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hA : 4 ≤ A) (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (anchor : ZMod s) (hanchor : Interior s t (PhaseCellBand.width p u) anchor)
    (hpad : intervalLength s t (PhaseCellBand.width p u) (phaseIndex s t anchor.val) +
      intervalLength s t (PhaseCellBand.width p u) (phaseIndex s t anchor.val) ≤ 2 ^ l + 1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l j rhsExp) (C k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (interiorSet s t (PhaseCellBand.width p u)) x
      (fun k => (value (executionPrecision p l j rhsExp) (C k)).re))
    (i : ℕ) (hi : i < intervalLength s t (PhaseCellBand.width p u) (phaseIndex s t anchor.val))
    (tail : List (Fin (A + 4))) :
    let phase := phaseIndex s t anchor.val
    let lo : ZMod s := (intervalStart s t (PhaseCellBand.width p u) phase : ℕ)
    let L := intervalLength s t (PhaseCellBand.width p u) phase
    let q := executionPrecision p l j rhsExp
    let w := executionWidth p l j rhsExp
    |(value q (decodeWord (((cstream A w
      (publishedWords 1 L (executedOutputWords s t p u q l 1 L (executionStagePrecision p l j rhsExp)
        (sourceExponent l j rhsExp) (fun _ => lo) (fun _ => C))) ++ tail).drop (i * w)).take w))).re -
      x (lo + (i : ZMod s))| ≤ 1 / (2 : ℝ) ^ j := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hphase : cell s t anchor = phaseIndex s t anchor.val := (phaseIndex_eq hs anchor.val).symm
  obtain ⟨hL, hfit, hint, hcell, hmax⟩ := generatedInterval_solver_geometry hst
    (PhaseCellBand.width p u) (phaseIndex s t anchor.val) anchor ⟨hanchor, hphase⟩
  simpa only [Fin.val_zero, Nat.zero_mul, Nat.zero_add] using publishedCell_accuracy
    (M := 1) hA hp hst hu hαu hθ hgap hbudget hL hpad
    (fun _ => ((intervalStart s t (PhaseCellBand.width p u) (phaseIndex s t anchor.val) : ℕ) : ZMod s))
    (fun _ => C) (fun _ _ k => hC k) (0 : Fin 1)
    (interiorSet s t (PhaseCellBand.width p u)) x hx hfit hint hcell hmax ⟨i, hi⟩ tail

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
