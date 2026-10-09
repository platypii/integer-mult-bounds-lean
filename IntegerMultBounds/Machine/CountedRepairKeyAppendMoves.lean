import IntegerMultBounds.Machine.CountedRepairKeyPrefix
import IntegerMultBounds.Machine.Branch
import IntegerMultBounds.Machine.MarkedReturn

/-! Four-tape physical moves used by the conditional repair-key writer. -/
namespace IntegerMultBounds.Machine.CountedRepairKeyAppendMoves
noncomputable section
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)
open CountedRankSplitBank (placed_exact)

def bank (F K V W : ℤ → Fin 5) (pf pk pv pw : ℤ) : Tapes 4 1 :=
  ⟨![pf,pk,pv,pw],![F,K,V,W]⟩

def flagPlace : Fin (2+2) ≃ Fin 4 := Equiv.refl _
def vPlace : Fin (2+2) ≃ Fin 4 where
  toFun := ![2,1,0,3]
  invFun := ![2,1,0,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def wPlace : Fin (2+2) ≃ Fin 4 where
  toFun := ![3,1,0,2]
  invFun := ![2,1,3,0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def copyFlag := Placement.placed (CopyWord.program (a := 1)) flagPlace
def copyV := Placement.placed (CopyWord.program (a := 1)) vPlace
def copyW := Placement.placed (CopyWord.program (a := 1)) wPlace
def leftAt (i : Fin 4) := Placement.placed (StepLeft.program (a := 1)) (FiniteReturnStackAt.placement i)
def backAt (i : Fin 4) := Placement.placed (ReturnOrigin.program (a := 1)) (FiniteReturnStackAt.placement i)
def keyBack := Placement.placed MarkedReturn.program (FiniteReturnStackAt.placement (1 : Fin 4))

theorem left_runs (v : Tapes 4 1) (i : Fin 4) :
    HoareTime (leftAt i) (fun w => w=v)
      (fun w => w=setTape v i (v.tape i) (v.head i-1)) 1 := by
  have h := Placement.hoare_at (StepLeft.step_hoare (v.tape i) (v.head i))
    (FiniteReturnStackAt.placement i) v (by rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  change setTape v i (v.tape i) (v.head i + -1) = _
  rw [sub_eq_add_neg]

theorem back_runs (v : Tapes 4 1) (i : Fin 4) (xs : List Bool)
    (ht : v.tape i=word xs) (hp : v.head i=xs.length) :
    HoareTime (backAt i) (fun w => w=v)
      (fun w => w=setTape v i (word xs) 0) (xs.length+2) := by
  have h0 := ReturnOrigin.return_hoare (a := 1) (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs)
  simp only [List.length_map] at h0
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  rfl

theorem keyBack_runs (v : Tapes 4 1) (xs : List (Fin 5))
    (ht : v.tape 1=FlagCopy.keyTape xs) (hp : v.head 1=xs.length)
    (hx : ∀ x ∈ xs, x≠blank ∧ x≠PartitionMarked.marker) :
    HoareTime keyBack (fun w => w=v)
      (fun w => w=setTape v 1 (FlagCopy.keyTape xs) 0) (xs.length+2) := by
  have h0 := MarkedReturn.return_hoare (PartitionMarked.markedTape 0 []) 0 xs hx rfl
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement (1 : Fin 4)) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; first | rfl | (simp only [zero_add]; rfl))
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  rfl

theorem copyFlag_runs (K V W : ℤ → Fin 5) (pk pv pw : ℤ) (fl : Bool) :
    HoareTime copyFlag (fun v => v=bank (word [fl]) K V W 0 pk pv pw)
      (fun v => v=bank (word [fl]) (putWord K pk [bitSymbol fl]) V W 1 (pk+1) pv pw) 1 := by
  apply placed_exact flagPlace _ _ _ _ _ _ _
    (CopyWord.copy_hoare (fun _ => blank) K 0 pk [bitSymbol fl]
      (ReturnOrigin.bits_nonblank [fl]) rfl)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem copyV_runs (F K W : ℤ → Fin 5) (pf pk pw : ℤ) (xs : List Bool) :
    HoareTime copyV (fun v => v=bank F K (word xs) W pf pk 0 pw)
      (fun v => v=bank F (putWord K pk (xs.map bitSymbol)) (word xs) W
        pf (pk+xs.length) xs.length pw) xs.length := by
  have h0 := CopyWord.copy_hoare (a := 1) (fun _ => blank) K 0 pk (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl
  simp only [List.length_map,zero_add] at h0
  apply placed_exact vPlace _ _ _ _ _ _ _ h0
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem copyW_runs (F K V : ℤ → Fin 5) (pf pk pv : ℤ) (xs : List Bool) :
    HoareTime copyW (fun v => v=bank F K V (word xs) pf pk pv 0)
      (fun v => v=bank F (putWord K pk (xs.map bitSymbol)) V (word xs)
        pf (pk+xs.length) pv xs.length) xs.length := by
  have h0 := CopyWord.copy_hoare (a := 1) (fun _ => blank) K 0 pk (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl
  simp only [List.length_map,zero_add] at h0
  apply placed_exact wPlace _ _ _ _ _ _ _ h0
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.CountedRepairKeyAppendMoves
