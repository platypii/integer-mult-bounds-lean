import IntegerMultBounds.Machine.CountedGuardConstantsEdit
import IntegerMultBounds.Machine.CountedGuardConstantsData
import IntegerMultBounds.Machine.CountedGuardGadgetHeaders

/-! Fixed eight-tape placements for original-header guard-constant production.
Only canonical q/b are original inputs. Shared fill/replay clock starts and
finishes blank; the synthesized q−1 descriptor and temporary one are explicit. -/
namespace IntegerMultBounds.Machine.CountedGuardConstantsPlacement
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)

def bank (qs bs ds : List Bool) (F1 F2 F3 : ℤ → Fin (a+4)) (p1 p2 p3 : ℤ) : Tapes 8 a :=
  ⟨![1,1,p1,p2,p3,1,0,0],![CountedLoopReuseAlphabet.binary qs,CountedLoopReuseAlphabet.binary bs,
    F1,F2,F3,CountedLoopReuseAlphabet.binary ds,fun _ => blank,fun _ => blank]⟩
def input (qs bs : List Bool) : Tapes 8 a := setTape (bank qs bs [] (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0) 5 (fun _ => blank) 0

def headerPlace : Fin (3+5) ≃ Fin 8 where
  toFun := ![0,6,5,1,2,3,4,7]
  invFun := ![0,3,4,5,6,2,1,7]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fill1Place : Fin (3+5) ≃ Fin 8 where
  toFun := ![2,7,5,0,1,3,4,6]
  invFun := ![3,4,0,5,6,2,7,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fill2Place : Fin (3+5) ≃ Fin 8 where
  toFun := ![3,7,5,0,1,2,4,6]
  invFun := ![3,4,5,0,6,2,7,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fill3Place : Fin (3+5) ≃ Fin 8 where
  toFun := ![4,7,1,0,2,3,5,6]
  invFun := ![3,2,4,5,0,6,7,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def edit1Place : Fin (3+5) ≃ Fin 8 where
  toFun := ![2,7,1,0,3,4,5,6]
  invFun := ![3,2,0,4,5,6,7,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def edit2Place : Fin (3+5) ≃ Fin 8 where
  toFun := ![3,7,1,0,2,4,5,6]
  invFun := ![3,2,4,0,5,6,7,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def setup := Placement.placed (CountedGuardGadgetHeaders.program (a := a)) headerPlace
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (5 : Fin 8)

theorem setsUp (qs bs : List Bool) (q : ℕ) (hq : Counter.value qs=q)
    (cq : GrowingCounterData.Canonical qs) (hp : 1 ≤ q) :
    HoareTime (setup (a := a)) (fun v => v=input qs bs)
      (fun v => v=bank qs bs (RecursiveChildQuotientsConstant.bits (q-1)) (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0) (6*q+44) := by
  have h := Placement.hoare_at (CountedGuardGadgetHeaders.constructs (a := a) qs q hq cq hp) headerPlace (input (a := a) qs bs) (by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change BinaryDescriptorStack.descriptor _=CountedLoopReuseAlphabet.binary _; rw [CountedGuardGadgetHeaders.binary_eq,BinaryDescriptorStackRoundtrip.descriptor_encoded])

def fill1 (x : Bool) := Placement.placed (CountedGuardConstantsFill.fill (a := a) x) fill1Place

theorem fills1 (x : Bool) (qs bs ds : List Bool) (F1 F2 F3 : ℤ → Fin (a+4))
    (p1 p2 p3 : ℤ) (n : ℕ) (hk : Counter.value ds=n) :
    HoareTime (fill1 (a := a) x) (fun v => v=bank qs bs ds F1 F2 F3 p1 p2 p3)
      (fun v => v=bank qs bs ds (putWord F1 p1 (List.replicate n (bitSymbol x))) F2 F3 (p1+n) p2 p3) (7*n+7*ds.length+23) := by
  have h := Placement.hoare_at (CountedGuardConstantsFill.fills (a := a) x F1 p1 ds n hk)
    fill1Place (bank (a := a) qs bs ds F1 F2 F3 p1 p2 p3) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def fill2 (x : Bool) := Placement.placed (CountedGuardConstantsFill.fill (a := a) x) fill2Place

theorem fills2 (x : Bool) (qs bs ds : List Bool) (F1 F2 F3 : ℤ → Fin (a+4))
    (p1 p2 p3 : ℤ) (n : ℕ) (hk : Counter.value ds=n) :
    HoareTime (fill2 (a := a) x) (fun v => v=bank qs bs ds F1 F2 F3 p1 p2 p3)
      (fun v => v=bank qs bs ds F1 (putWord F2 p2 (List.replicate n (bitSymbol x))) F3 p1 (p2+n) p3) (7*n+7*ds.length+23) := by
  have h := Placement.hoare_at (CountedGuardConstantsFill.fills (a := a) x F2 p2 ds n hk)
    fill2Place (bank (a := a) qs bs ds F1 F2 F3 p1 p2 p3) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def fill3 (x : Bool) := Placement.placed (CountedGuardConstantsFill.fill (a := a) x) fill3Place

theorem fills3 (x : Bool) (qs bs ds : List Bool) (F1 F2 F3 : ℤ → Fin (a+4))
    (p1 p2 p3 : ℤ) (n : ℕ) (hk : Counter.value bs=n) :
    HoareTime (fill3 (a := a) x) (fun v => v=bank qs bs ds F1 F2 F3 p1 p2 p3)
      (fun v => v=bank qs bs ds F1 F2 (putWord F3 p3 (List.replicate n (bitSymbol x))) p1 p2 (p3+n)) (7*n+7*bs.length+23) := by
  have h := Placement.hoare_at (CountedGuardConstantsFill.fills (a := a) x F3 p3 bs n hk)
    fill3Place (bank (a := a) qs bs ds F1 F2 F3 p1 p2 p3) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def rewind1 := Placement.placed (CountedGuardConstantsEdit.rewind (a := a)) edit1Place

theorem rewinds1 (qs bs ds : List Bool) (_F1 F2 F3 : ℤ → Fin (a+4))
    (_p1 p2 p3 : ℤ) (xs : List Bool) :
    HoareTime (rewind1 (a := a)) (fun v => v=bank qs bs ds (word xs) F2 F3 (xs.length) p2 p3)
      (fun v => v=bank qs bs ds (word xs) F2 F3 0 p2 p3) (xs.length+2) := by
  have h := Placement.hoare_at (CountedGuardConstantsEdit.rewind_hoare (a := a) xs bs)
    edit1Place (bank (a := a) qs bs ds (word xs) F2 F3 (xs.length) p2 p3) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def rewind2 := Placement.placed (CountedGuardConstantsEdit.rewind (a := a)) edit2Place

theorem rewinds2 (qs bs ds : List Bool) (F1 _F2 F3 : ℤ → Fin (a+4))
    (p1 _p2 p3 : ℤ) (xs : List Bool) :
    HoareTime (rewind2 (a := a)) (fun v => v=bank qs bs ds F1 (word xs) F3 p1 (xs.length) p3)
      (fun v => v=bank qs bs ds F1 (word xs) F3 p1 0 p3) (xs.length+2) := by
  have h := Placement.hoare_at (CountedGuardConstantsEdit.rewind_hoare (a := a) xs bs)
    edit2Place (bank (a := a) qs bs ds F1 (word xs) F3 p1 (xs.length) p3) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def rewind3 := Placement.placed (CountedGuardConstantsEdit.rewind (a := a)) fill3Place

theorem rewinds3 (qs bs ds : List Bool) (F1 F2 _F3 : ℤ → Fin (a+4))
    (p1 p2 _p3 : ℤ) (xs : List Bool) :
    HoareTime (rewind3 (a := a)) (fun v => v=bank qs bs ds F1 F2 (word xs) p1 p2 (xs.length))
      (fun v => v=bank qs bs ds F1 F2 (word xs) p1 p2 0) (xs.length+2) := by
  have h := Placement.hoare_at (CountedGuardConstantsEdit.rewind_hoare (a := a) xs bs)
    fill3Place (bank (a := a) qs bs ds F1 F2 (word xs) p1 p2 (xs.length)) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def edit1 (x : Bool) := Placement.placed (CountedGuardConstantsEdit.program (a := a) x) edit1Place

theorem edits1 (x : Bool) (qs bs ds : List Bool) (F1 F2 F3 : ℤ → Fin (a+4))
    (_p1 p2 p3 : ℤ) (b : ℕ) (hk : Counter.value bs=b) :
    HoareTime (edit1 (a := a) x) (fun v => v=bank qs bs ds F1 F2 F3 0 p2 p3)
      (fun v => v=bank qs bs ds (Function.update F1 (b+1 : ℕ) (bitSymbol x)) F2 F3 0 p2 p3) (14*b+14*bs.length+55) := by
  have h := Placement.hoare_at (CountedGuardConstantsEdit.runs (a := a) x F1 bs b hk)
    edit1Place (bank (a := a) qs bs ds F1 F2 F3 0 p2 p3) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def edit2 (x : Bool) := Placement.placed (CountedGuardConstantsEdit.program (a := a) x) edit2Place

theorem edits2 (x : Bool) (qs bs ds : List Bool) (F1 F2 F3 : ℤ → Fin (a+4))
    (p1 _p2 p3 : ℤ) (b : ℕ) (hk : Counter.value bs=b) :
    HoareTime (edit2 (a := a) x) (fun v => v=bank qs bs ds F1 F2 F3 p1 0 p3)
      (fun v => v=bank qs bs ds F1 (Function.update F2 (b+1 : ℕ) (bitSymbol x)) F3 p1 0 p3) (14*b+14*bs.length+55) := by
  have h := Placement.hoare_at (CountedGuardConstantsEdit.runs (a := a) x F2 bs b hk)
    edit2Place (bank (a := a) qs bs ds F1 F2 F3 p1 0 p3) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def write3 := Placement.placed (CountedGuardConstantsFill.cell (a := a) false) (FiniteReturnStackAt.placement (4 : Fin 8))
def left3 := Placement.placed (StepLeft.program (a := a)) (FiniteReturnStackAt.placement (4 : Fin 8))

theorem writes3 (qs bs ds : List Bool) (F1 F2 F3 : ℤ → Fin (a+4)) (p1 p2 p3 : ℤ) :
    HoareTime (write3 (a := a)) (fun v => v=bank qs bs ds F1 F2 F3 p1 p2 p3)
      (fun v => v=bank qs bs ds F1 F2 (Function.update F3 p3 (bitSymbol false)) p1 p2 (p3+1)) 1 := by
  have h := Placement.hoare_at (CountedGuardConstantsFill.cell_hoare (a := a) false F3 p3)
    (FiniteReturnStackAt.placement (4 : Fin 8)) (bank (a := a) qs bs ds F1 F2 F3 p1 p2 p3)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem lefts3 (qs bs ds : List Bool) (F1 F2 F3 : ℤ → Fin (a+4)) (p1 p2 p3 : ℤ) :
    HoareTime (left3 (a := a)) (fun v => v=bank qs bs ds F1 F2 F3 p1 p2 p3)
      (fun v => v=bank qs bs ds F1 F2 F3 p1 p2 (p3-1)) 1 := by
  have h := Placement.hoare_at (StepLeft.step_hoare (a := a) F3 p3)
    (FiniteReturnStackAt.placement (4 : Fin 8)) (bank (a := a) qs bs ds F1 F2 F3 p1 p2 p3)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.CountedGuardConstantsPlacement
