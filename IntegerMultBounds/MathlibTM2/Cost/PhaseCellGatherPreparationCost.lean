module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGatherPreparation
import Mathlib.Tactic.Ring

/-! The shared conversion visits eleven scalar sources once. Replica count is
kept separate from scalar setup and encoded-stream movement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry

/-- Sum the fixed scalar schema, without specializing a caller or row bank. -/
theorem globalConversionCost_eq (D p u l target s t B W N radius width : ℕ) :
    globalConversionCost D p u l target s t B W N radius width =
      (p+u+l+target+s+t+B+W+N+radius+width)*(4*D+10)+44*D+89 := by
  simp only [globalConversionCost,List.ofFn_succ,List.ofFn_zero,List.sum_cons,List.sum_nil,globalValues]
  simp
  ring

theorem gatherPreparationCost_eq (D p u l target s t B W N radius width Vg Vr : ℕ) :
    gatherPreparationCost D p u l target s t B W N radius width Vg Vr =
      (p+u+l+target+s+t+B+W+radius+width)*(4*D+10)+44*D+34*(B+Vg+Vr)+
        4*W+4*s*W+9*s+209+N*(4*D+14) := by
  rw [gatherPreparationCost,callerInputCost,globalConversionCost_eq,movementControlCost]
  ring

theorem gatherPreparationCost_le (D p u l target s t B W N radius width Vg Vr : ℕ)
    (hVg : Vg ≤ D) (hVr : Vr ≤ D) :
    gatherPreparationCost D p u l target s t B W N radius width Vg Vr ≤
      (p+u+l+target+s+t+B+W+radius+width)*(4*D+10)+112*D+34*B+
        4*W+4*s*W+9*s+209+N*(4*D+14) := by
  rw [gatherPreparationCost_eq]
  omega

end IntegerMultBounds.MathlibTM2.Cost
