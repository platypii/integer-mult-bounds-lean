import IntegerMultBounds.Machine.CountedGuardConstantsFill
import IntegerMultBounds.Machine.CountedGuardGadgetFinish

/-! Fixed-control overwrite at the cell b+1 using the original b descriptor,
with real outward movement and replay to the origin. Exact complete tapes,
including padded high bits, are retained except for the chosen cell. -/
namespace IntegerMultBounds.Machine.CountedGuardConstantsEdit
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet
def bank := CountedGuardConstantsFill.input (a := a)
open CountedGuardGadgetRecord (word)

def stepRight := Placement.placed (StepRight.program (a := a)) (FiniteReturnStackAt.placement (0 : Fin 3))
def stepLeft := Placement.placed (StepLeft.program (a := a)) (FiniteReturnStackAt.placement (0 : Fin 3))
def write (b : Bool) := Placement.placed (CountedGuardConstantsFill.cell (a := a) b) (FiniteReturnStackAt.placement (0 : Fin 3))
def rewind := Placement.placed (ReturnOrigin.program (a := a)) (FiniteReturnStackAt.placement (0 : Fin 3))

theorem stepRight_hoare (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) :
    HoareTime (stepRight (a := a)) (fun v => v=bank f p ks)
      (fun v => v=bank f (p+1) ks) 1 := by
  have h := Placement.hoare_at (StepRight.step_hoare (a := a) f p)
    (FiniteReturnStackAt.placement (0 : Fin 3)) (bank (a := a) f p ks) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem stepLeft_hoare (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) :
    HoareTime (stepLeft (a := a)) (fun v => v=bank f p ks)
      (fun v => v=bank f (p-1) ks) 1 := by
  have h := Placement.hoare_at (StepLeft.step_hoare (a := a) f p)
    (FiniteReturnStackAt.placement (0 : Fin 3)) (bank (a := a) f p ks) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem write_hoare (b : Bool) (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) :
    HoareTime (write (a := a) b) (fun v => v=bank f p ks)
      (fun v => v=bank (Function.update f p (bitSymbol b)) (p+1) ks) 1 := by
  have h := Placement.hoare_at (CountedGuardConstantsFill.cell_hoare (a := a) b f p)
    (FiniteReturnStackAt.placement (0 : Fin 3)) (bank (a := a) f p ks) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rewind_hoare (xs : List Bool) (ks : List Bool) :
    HoareTime (rewind (a := a)) (fun v => v=bank (word xs) xs.length ks)
      (fun v => v=bank (word xs) 0 ks) (xs.length+2) := by
  have h0 := ReturnOrigin.return_hoare (xs.map (bitSymbol (a := a))) (ReturnOrigin.bits_nonblank xs)
  simp only [List.length_map] at h0
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement (0 : Fin 3))
    (bank (a := a) (word xs) xs.length ks) (by rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program (x : Bool) := seq (seq (seq (seq (seq
  (CountedGuardConstantsFill.position (a := a) Move.right) stepRight) (write x))
  (CountedGuardConstantsFill.position Move.left)) stepLeft) stepLeft

theorem runs (x : Bool) (f : ℤ → Fin (a+4)) (ks : List Bool) (b : ℕ) (hk : Counter.value ks=b) :
    HoareTime (program (a := a) x) (fun v => v=bank f 0 ks)
      (fun v => v=bank (Function.update f (b+1 : ℕ) (bitSymbol x)) 0 ks)
      (14*b+14*ks.length+55) := by
  let F := Function.update f (b+1 : ℕ) (bitSymbol (a := a) x)
  have h1 := CountedGuardConstantsFill.positions (a := a) Move.right f 0 ks b hk
  simp only [Move.offset,mul_one,zero_add] at h1
  have h2 := stepRight_hoare (a := a) f b ks
  have h3 := write_hoare (a := a) x f ((b : ℤ)+1) ks
  have hc : ((b+1 : ℕ) : ℤ)=(b : ℤ)+1 := by push_cast; rfl
  rw [← hc] at h2 h3
  have h4 := CountedGuardConstantsFill.positions (a := a) Move.left F (((b+1 : ℕ) : ℤ)+1) ks b hk
  simp only [Move.offset,mul_neg_one] at h4
  rw [show (((b+1 : ℕ) : ℤ)+1)+(-(b : ℤ))=2 by push_cast; omega] at h4
  have h5 := stepLeft_hoare (a := a) F 2 ks
  have h6 := stepLeft_hoare (a := a) F 1 ks
  exact (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedGuardConstantsEdit
