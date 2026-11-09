module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.NLogN.PhaseCellCoreWindows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundDimensions

/-! Common publication contract for bulk and seam coefficient rows. The byte
width is explicit; replica order is the order of the input list. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix PhaseCellInterface

def ExactCoreRows {A s : ℕ} [NeZero s] (p W width k : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) : Prop :=
  rows.length = Fs.length ∧
    (∀ row ∈ rows, row.length = coreLength s width k) ∧
    List.Forall₂ (fun F row =>
      let out := packedIntervalRead p W (coreStart width k) (cstream A W row)
      (∀ i ∈ ownedCore s width k, ‖out i‖ ≤ 1) ∧
      ErrorOn (ownedCore s width k) out
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun i => value p (F i)))
        (3/(2 : ℝ)^p)) Fs rows

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
