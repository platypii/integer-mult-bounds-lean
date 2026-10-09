import IntegerMultBounds.Machine.CountedGuardConstants
import IntegerMultBounds.Machine.CountedGuardGadget

/-! Fixed fifteen-tape guard initialization from original q/b/n headers and
literal V/W alone. The three comparison constants are physically synthesized
in the existing private workspace, with all workspace returned blank. -/
namespace IntegerMultBounds.Machine.CountedGuardOriginalSetup
noncomputable section
variable {a : ℕ}
open CountedGuardConstantsData

def input (V W : List Bool) (bs ns qs : List Bool) : Tapes 15 a :=
  CountedGuardGadget.input V W [] [] [] bs ns qs

def prepared (q b : ℕ) (V W : List Bool) (bs ns qs : List Bool) : Tapes 15 a :=
  CountedGuardGadget.input V W (c1 q b) (c2 q b) (c3 b) bs ns qs

def constantsPlace : Fin (8+7) ≃ Fin 15 where
  toFun := ![13,9,2,3,4,8,14,7,0,1,5,6,10,11,12]
  invFun := ![8,9,2,3,4,10,11,7,5,1,12,13,14,0,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program := Placement.placed (CountedGuardConstants.program (a := a)) constantsPlace

theorem runs (q b : ℕ) (V W : List Bool) (bs ns qs : List Bool)
    (hq : Counter.value qs=q) (cq : GrowingCounterData.Canonical qs)
    (hvb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs)
    (hb : 1 ≤ b) (hbq : b+3 ≤ q) :
    HoareTime (program (a := a)) (fun v => v=input V W bs ns qs)
      (fun v => v=prepared q b V W bs ns qs) (40*q+80*b+300) := by
  have h := Placement.hoare_at (CountedGuardConstants.runs (a := a) q b qs bs hq cq hvb cb hb hbq)
    constantsPlace (input (a := a) V W bs ns qs) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem input_private (V W : List Bool) (bs ns qs : List Bool) (i : Fin 15)
    (hi : i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=10 ∨ i=11 ∨ i=14) :
    (input (a := a) V W bs ns qs).tape i=(fun _ => blank) ∧
    (input (a := a) V W bs ns qs).head i=0 := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.CountedGuardOriginalSetup
