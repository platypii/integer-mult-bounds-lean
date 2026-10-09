import IntegerMultBounds.Machine.ActiveRepairRankFieldsField

/-! Runtime fixed-width overwrite at an address supplied on an unchanged header.
The replacement, both headers and all heads are retained; clock work is erased. -/
namespace IntegerMultBounds.Machine.ActiveRepairDestinationPatchOverwrite
noncomputable section
open ActiveRepairRankFieldsField
variable {a : ℕ}

def outputStartPlace : Fin (3+2) ≃ Fin 5 where
  toFun := ![1,4,2,0,3]
  invFun := ![3,0,2,4,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def seek := Placement.placed (ActiveRepairRankFieldsPosition.program (a := a) .right) outputStartPlace
def back := Placement.placed (ActiveRepairRankFieldsPosition.program (a := a) .left) outputStartPlace

def program := seq (seq (seq (seq (seek (a := a)) copy) outputBack) back) sourceBackWidth

theorem seeks (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool)
    (start : ℕ) (hv : Counter.value (hs 0)=start) :
    HoareTime (seek (a := a)) (fun v => v=bank f g p q hs)
      (fun v => v=bank f g p (q+start) hs) (7*start+7*(hs 0).length+28) := by
  have h := ActiveRepairRankFieldsPosition.runs .right g q (hs 0) start hv
  simp only [Move.offset,mul_one] at h
  apply CountedRankSplitBank.placed_exact outputStartPlace _ _ _ _ _ _ _ h
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem backs (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool)
    (start : ℕ) (hv : Counter.value (hs 0)=start) :
    HoareTime (back (a := a)) (fun v => v=bank f g p q hs)
      (fun v => v=bank f g p (q-start) hs) (7*start+7*(hs 0).length+28) := by
  have h := ActiveRepairRankFieldsPosition.runs .left g q (hs 0) start hv
  simp only [Move.offset,mul_neg_one] at h
  apply CountedRankSplitBank.placed_exact outputStartPlace _ _ _ _ _ _ _ h
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs_raw (f g : ℤ → Fin (a+4)) (p q : ℤ) (hs : Fin 2 → List Bool)
    (start width : ℕ) (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=width) :
    HoareTime (program (a := a)) (fun v => v=bank f g p q hs)
      (fun v => v=bank f (putWord g (q+start) (CopyCells.cells f p width)) p q hs)
      (cost start width hs) := by
  let out := putWord g (q+start) (CopyCells.cells f p width)
  have h0 := seeks f g p q hs start hv0
  have h1 := copies f g p (q+start) hs width hv1
  have h2 := output_back f out (p+width) ((q+start)+width) hs width hv1
  simp only [add_sub_cancel_right] at h2
  have h3 := backs f out (p+width) (q+start) hs start hv0
  simp only [add_sub_cancel_right] at h3
  have h4 := source_back_width f out (p+width) q hs width hv1
  simp only [add_sub_cancel_right] at h4
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

/-- A counted copy reads exactly the replacement width, so no delimiter or
blank-tail hypothesis is needed on its source word. -/
theorem replacement_cells (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List Bool) :
    CopyCells.cells (putWord f p (xs.map bitSymbol)) p xs.length=xs.map bitSymbol := by
  induction xs generalizing f p with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.length_cons,List.map_cons,CopyCells.cells,putWord_head]
    rw [putWord_cons,ih]
    cases b <;> rfl

/-- Physical overwrite by an explicit fixed-width replacement; every other
cell of the destination is retained by `putWord`. -/
theorem runs (f g : ℤ → Fin (a+4)) (p q : ℤ) (xs : List Bool) (hs : Fin 2 → List Bool)
    (start : ℕ) (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=xs.length) :
    HoareTime (program (a := a))
      (fun v => v=bank (putWord f p (xs.map bitSymbol)) g p q hs)
      (fun v => v=bank (putWord f p (xs.map bitSymbol))
        (putWord g (q+start) (xs.map bitSymbol)) p q hs)
      (cost start xs.length hs) := by
  simpa only [replacement_cells] using
    runs_raw (putWord f p (xs.map bitSymbol)) g p q hs start xs.length hv0 hv1

 theorem runs_linear (f g : ℤ → Fin (a+4)) (p q : ℤ) (xs : List Bool) (hs : Fin 2 → List Bool)
    (start : ℕ) (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=xs.length)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a))
      (fun v => v=bank (putWord f p (xs.map bitSymbol)) g p q hs)
      (fun v => v=bank (putWord f p (xs.map bitSymbol))
        (putWord g (q+start) (xs.map bitSymbol)) p q hs)
      (200*(start+xs.length+1)) :=
  (runs f g p q xs hs start hv0 hv1).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear start xs.length hs hv0 hv1 hc)

end
end IntegerMultBounds.Machine.ActiveRepairDestinationPatchOverwrite
