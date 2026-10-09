import IntegerMultBounds.Machine.UnitPhaseNumerator
import IntegerMultBounds.Machine.FiniteReturnStackAt

/-! After the two results have been physically emitted and erased, both
retained numerator sources are cleared. The complete arithmetic bank returns
blank at zero; every source digit and marker is charged. -/
namespace IntegerMultBounds.Machine.UnitPhaseCoreReset
noncomputable section
open SharedPlacementAlphabet (setTape)

def real := Placement.placed (MarkedBinaryCleanup.program (q := 2))
  (FiniteReturnStackAt.placement (0 : Fin 6))
def imaginary := Placement.placed (MarkedBinaryCleanup.program (q := 2))
  (FiniteReturnStackAt.placement (1 : Fin 6))
def program := seq real imaginary

theorem runs (xs : ℕ → List (Fin 2)) (w : ℕ) (hw : ∀ j,(xs j).length=w) :
    HoareTime program (fun v => v=UnitPhaseNumerator.coreInput xs)
      (fun v => v=SharedBank.empty 6 2) (4*w+9) := by
  let mid := setTape (UnitPhaseNumerator.coreInput xs) 0 (fun _ => blank) 0
  have h0 := Placement.hoare_at (RawLinearCombinationCleanup.marked_radix (xs 0))
    (FiniteReturnStackAt.placement (0 : Fin 6)) (UnitPhaseNumerator.coreInput xs)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  have hr : HoareTime real (fun v => v=UnitPhaseNumerator.coreInput xs) (fun v => v=mid)
      (2*(xs 0).length+4) := by
    apply h0.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨small,rfl,rfl⟩
    exact FiniteReturnStackAt.replace_bank _ _ _ _
  have h1 := Placement.hoare_at (RawLinearCombinationCleanup.marked_radix (xs 1))
    (FiniteReturnStackAt.placement (1 : Fin 6)) mid
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  have hi : HoareTime imaginary (fun v => v=mid) (fun v => v=SharedBank.empty 6 2)
      (2*(xs 1).length+4) := by
    apply h1.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨small,rfl,rfl⟩
    change Placement.replace (FiniteReturnStackAt.placement (1 : Fin 6)) mid
      (FiniteReturnStack.bank (fun _ => blank) 0)=SharedBank.empty 6 2
    rw [FiniteReturnStackAt.replace_bank]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  exact (hr.seq hi).consequence (fun _ h => h) (fun _ h => h) (by rw [hw 0,hw 1]; omega)

theorem emitted_core (p : Fin 4) (xs : ℕ → List (Fin 2)) :
    setTape (setTape (UnitPhaseNumerator.coreOutput p xs) 2 (fun _ => blank) 0)
      4 (fun _ => blank) 0=UnitPhaseNumerator.coreInput xs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.UnitPhaseCoreReset
