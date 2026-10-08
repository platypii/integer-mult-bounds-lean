import IntegerMultBounds.Machine.FlatCoordinateInitializedSchedule
import IntegerMultBounds.Machine.RunSupport

/-! Explicit support bounds for the generated private workspace of actual
initialized mixed schedules. These are derived from verified physical runtime;
they are preparation for cleanup, not an assertion of a cleanup machine. -/
namespace IntegerMultBounds.Machine.FlatCoordinateScheduleSupport
open FlatCoordinateInitializedSchedule
open ActualAffineScaling (modulus)
open Networks.Shared50ModularControl (prime)
noncomputable section
variable {d : ℕ}
local instance (b : ℕ) : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- Every private head and nonblank private cell lies in this known linear
interval after execution from the literal common-four-plus-blank input. -/
def PrivateBound {t : ℕ} (v : Tapes t prime) (bound : ℕ) : Prop :=
  ∀ i : Fin t, 4 ≤ i.val →
    -(bound : ℤ) ≤ v.head i ∧ v.head i ≤ bound ∧
      ∀ z, z < -(bound : ℤ) ∨ (bound : ℤ) < z → v.tape i z = blank

theorem output_support (ops : List (FlatCoordinateSchedule.Op d)) (b W : ℕ)
    (a : FlatCoordinateStages.Array d b W) (w : Tapes (skeleton ops).tapes prime) (bound : ℕ)
    (h : HoareTime (skeleton ops).program (fun v => v = FlatCoordinateInitializedSchedule.input ops b W a)
      (fun v => v = w) bound) : PrivateBound w bound := by
  intro i hi
  have hh : (FlatCoordinateInitializedSchedule.input ops b W a).head i = 0 := by
    simp only [FlatCoordinateInitializedSchedule.input,SharedBankStageInput.raw,dite_eq_right (by omega : ¬ i.val < 4)]
  have ht : (FlatCoordinateInitializedSchedule.input ops b W a).tape i = fun _ => blank := by
    simp only [FlatCoordinateInitializedSchedule.input,SharedBankStageInput.raw,dite_eq_right (by omega : ¬ i.val < 4)]
  exact RunSupport.hoare_blank _ _ _ _ h i hh ht

/-- The existing actual schedule witness has linear-volume private support,
while retaining its exact common-bank output and ordered affine semantics. -/
theorem realizes_with_support (ops : List (FlatCoordinateSchedule.Op d)) (b W : ℕ) (hW : 0 < W) :
    ∃ output : FlatCoordinateStages.Array d b W → Tapes (skeleton ops).tapes prime,
      (∀ a, PrivateBound (output a) (constant ops*((modulus b)^d*W))) ∧
      (∀ a, HoareTime (skeleton ops).program (fun v => v = FlatCoordinateInitializedSchedule.input ops b W a)
        (fun v => v = output a ∧
          SharedBank.payload v (skeleton ops).slots =
            FlatCoordinateShiftSharedBank.common (array ops b W hW a) ∧
          ∀ (x : Fin d → ZMod (modulus b)) (j : Fin W),
            array ops b W hW a
              (FlatCoordinateLayout.index (Networks.OrderedAffine.run (ops.map (fun op => op.action b)) x) j) =
                a (FlatCoordinateLayout.index x j))
        (constant ops*((modulus b)^d*W))) := by
  obtain ⟨output,hh⟩ := realizes ops b W hW
  refine ⟨output,?_,hh⟩
  intro a
  apply output_support ops b W a (output a)
  exact (hh a).consequence (fun _ h => h) (fun _ h => h.1) le_rfl

end
end IntegerMultBounds.Machine.FlatCoordinateScheduleSupport
