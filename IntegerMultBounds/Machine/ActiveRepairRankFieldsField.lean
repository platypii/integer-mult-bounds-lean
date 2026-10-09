import IntegerMultBounds.Machine.ActiveRepairRankFieldsPosition
import IntegerMultBounds.Machine.CountedRankSplitBank
import IntegerMultBounds.Machine.CountedRankSplitData

/-! One fixed five-tape machine extracts a runtime start/width field from a
possibly short counter. Source/output heads and original headers are restored;
zero extension is by actual blank cells and all clock work is physically erased. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankFieldsField
noncomputable section
variable {a : ℕ}

def bank (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool) : Tapes 5 a :=
  ⟨![p,q,1,1,0],![f,g,RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),fun _ => blank]⟩

def startPlace : Fin (3+2) ≃ Fin 5 where
  toFun := ![0,4,2,1,3]
  invFun := ![0,3,2,4,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def sourceWidthPlace : Fin (3+2) ≃ Fin 5 where
  toFun := ![0,4,3,1,2]
  invFun := ![0,3,4,2,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def outputWidthPlace : Fin (3+2) ≃ Fin 5 where
  toFun := ![1,4,3,0,2]
  invFun := ![3,0,4,2,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def copyPlace : Fin (4+1) ≃ Fin 5 where
  toFun := ![0,1,4,3,2]
  invFun := ![0,1,4,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def seek := Placement.placed (ActiveRepairRankFieldsPosition.program (a := a) .right) startPlace
def copy := Placement.placed (CountedRankSplitCopy.program (a := a)) copyPlace
def sourceBackWidth := Placement.placed (ActiveRepairRankFieldsPosition.program (a := a) .left) sourceWidthPlace
def sourceBackStart := Placement.placed (ActiveRepairRankFieldsPosition.program (a := a) .left) startPlace
def outputBack := Placement.placed (ActiveRepairRankFieldsPosition.program (a := a) .left) outputWidthPlace

def program := seq (seq (seq (seq (seek (a := a)) copy) sourceBackWidth) sourceBackStart) outputBack

theorem seeks (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool)
    (start : ℕ) (hv : Counter.value (hs 0)=start) :
    HoareTime (seek (a := a)) (fun v => v=bank f g p q hs)
      (fun v => v=bank f g (p+start) q hs) (7*start+7*(hs 0).length+28) := by
  have h := ActiveRepairRankFieldsPosition.runs .right f p (hs 0) start hv
  simp only [Move.offset,mul_one] at h
  apply CountedRankSplitBank.placed_exact startPlace _ _ _ _ _ _ _ h
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem copies (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool)
    (width : ℕ) (hv : Counter.value (hs 1)=width) :
    HoareTime (copy (a := a)) (fun v => v=bank f g p q hs)
      (fun v => v=bank f (putWord g q (CopyCells.cells f p width)) (p+width) (q+width) hs)
      (7*width+7*(hs 1).length+28) := by
  apply CountedRankSplitBank.placed_exact copyPlace _ _ _ _ _ _ _
    (CountedRankSplitCopy.copies f g p q (hs 1) width hv)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem source_back_width (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool)
    (width : ℕ) (hv : Counter.value (hs 1)=width) :
    HoareTime (sourceBackWidth (a := a)) (fun v => v=bank f g p q hs)
      (fun v => v=bank f g (p-width) q hs) (7*width+7*(hs 1).length+28) := by
  have h := ActiveRepairRankFieldsPosition.runs .left f p (hs 1) width hv
  simp only [Move.offset,mul_neg_one] at h
  apply CountedRankSplitBank.placed_exact sourceWidthPlace _ _ _ _ _ _ _ h
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem source_back_start (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool)
    (start : ℕ) (hv : Counter.value (hs 0)=start) :
    HoareTime (sourceBackStart (a := a)) (fun v => v=bank f g p q hs)
      (fun v => v=bank f g (p-start) q hs) (7*start+7*(hs 0).length+28) := by
  have h := ActiveRepairRankFieldsPosition.runs .left f p (hs 0) start hv
  simp only [Move.offset,mul_neg_one] at h
  apply CountedRankSplitBank.placed_exact startPlace _ _ _ _ _ _ _ h
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem output_back (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool)
    (width : ℕ) (hv : Counter.value (hs 1)=width) :
    HoareTime (outputBack (a := a)) (fun v => v=bank f g p q hs)
      (fun v => v=bank f g p (q-width) hs) (7*width+7*(hs 1).length+28) := by
  have h := ActiveRepairRankFieldsPosition.runs .left g q (hs 1) width hv
  simp only [Move.offset,mul_neg_one] at h
  apply CountedRankSplitBank.placed_exact outputWidthPlace _ _ _ _ _ _ _ h
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def cost (start width : ℕ) (hs : Fin 2 → List Bool) :=
  14*start+21*width+14*(hs 0).length+21*(hs 1).length+144

theorem runs_raw (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool)
    (start width : ℕ) (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=width) :
    HoareTime (program (a := a)) (fun v => v=bank f g p q hs)
      (fun v => v=bank f (putWord g q (CopyCells.cells f (p+start) width)) p q hs)
      (cost start width hs) := by
  let out := putWord g q (CopyCells.cells f (p+start) width)
  have h0 := seeks f g p q hs start hv0
  have h1 := copies f g (p+start) q hs width hv1
  have h2 := source_back_width f out ((p+start)+width) (q+width) hs width hv1
  simp only [add_sub_cancel_right] at h2
  have h3 := source_back_start f out (p+start) (q+width) hs start hv0
  simp only [add_sub_cancel_right] at h3
  have h4 := output_back f out p (q+width) hs width hv1
  simp only [add_sub_cancel_right] at h4
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

/-- No stored-counter length condition: every high output bit is read from
actual blank cells and written as a literal zero, with all traversals paid. -/
theorem runs (f g : ℤ → Fin (a+4)) (q : ℤ) (cs : List Bool) (hs : Fin 2 → List Bool)
    (start width : ℕ) (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=width)
    (ht : ∀ z : ℤ, 1+cs.length≤z → f z=blank) :
    HoareTime (program (a := a))
      (fun v => v=bank (putWord f 1 (cs.map bitSymbol)) g 1 q hs)
      (fun v => v=bank (putWord f 1 (cs.map bitSymbol))
        (putWord g q ((Gather.field cs start width).map bitSymbol)) 1 q hs)
      (cost start width hs) := by
  simpa only [CountedRankSplitData.cells_word f cs ht start width] using
    runs_raw (putWord f 1 (cs.map bitSymbol)) g 1 q hs start width hv0 hv1

theorem cost_linear (start width : ℕ) (hs : Fin 2 → List Bool)
    (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=width)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost start width hs≤200*(start+width+1) := by
  have h0 := GrowingCounterData.canonical_width (hs 0) (hc 0)
  have h1 := GrowingCounterData.canonical_width (hs 1) (hc 1)
  rw [hv0] at h0
  rw [hv1] at h1
  have l0 := Nat.log2_le_self start
  have l1 := Nat.log2_le_self width
  unfold cost
  omega

end
end IntegerMultBounds.Machine.ActiveRepairRankFieldsField
