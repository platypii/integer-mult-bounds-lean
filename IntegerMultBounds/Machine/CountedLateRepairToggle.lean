import IntegerMultBounds.Machine.CountedLateRepairPrefix

/-! The later repair physically applies the ideal low-bit toggle to the
recovered target, retaining both recovered dirty words and the original flag. -/
namespace IntegerMultBounds.Machine.CountedLateRepairToggle
noncomputable section
open SharedPlacementAlphabet (setTape)
open CountedGuardGadgetRecord (word)
open CountedRankSplitBank (placed_exact)

def working (V W U X T : List Bool) (hs : Fin 3 → List Bool) (fl : Bool) : Tapes 31 1 :=
  ((CountedPackedLateRun.bank V W U X [] (fun _ => blank) (fun _ => blank)
    (fun _ => blank) (fun _ => blank) 0 0 0 0 hs).append (CountedLateRepairPrefix.flagBank fl)).append
      (FiniteReturnStack.bank (word T) 0)

def before (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X : List Bool) (hs : Fin 3 → List Bool) : Tapes 31 1 :=
  working (CountedLateRepairInverse.target q b hb hbq V W U X)
    (CountedLateRepairInverse.temp q b hb hbq V W U X) (CountedLateRepairInverse.restored b hb U X)
    X [] hs (CountedLateRepairGuard.flag q b V W X || CountedLateRepairGuard.flag q b V U X)
def after (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X : List Bool) (hs : Fin 3 → List Bool) : Tapes 31 1 :=
  working (CountedLateRepairInverse.target q b hb hbq V W U X)
    (CountedLateRepairInverse.temp q b hb hbq V W U X) (CountedLateRepairInverse.restored b hb U X)
    X (CountedIdealToggle.word q (CountedLateRepairInverse.target q b hb hbq V W U X) X)
    hs (CountedLateRepairGuard.flag q b V W X || CountedLateRepairGuard.flag q b V U X)

def place : Fin (22+9) ≃ Fin 31 where
  toFun := ![1,3,5,0,30,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,2,4,6,7,8,9,10,28,29]
  invFun := ![3,0,22,1,23,2,24,25,26,27,28,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,29,30,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem extra_ne (i : Fin 9) : place (Fin.natAdd 22 i) ≠ (30 : Fin 31) := by
  fin_cases i <;> decide

def program := Placement.placed (CountedIdealToggle.program 1) place

def view (V W X T : List Bool) (hs : Fin 3 → List Bool) : Tapes 22 1 :=
  CountedIdealToggle.bank (PackedLine.bank (word W) (word X) (fun _ => blank)
    (word V) (word T) 0 0 0 0 0) hs

theorem active_working (V W U X T : List Bool) (hs : Fin 3 → List Bool) (fl : Bool) :
    Placement.active place (working V W U X T hs fl)=view V W X T hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem extra_working (V W U X T1 T2 : List Bool) (hs : Fin 3 → List Bool) (fl : Bool) :
    Placement.extra place (working V W U X T1 hs fl)=
      Placement.extra place (working V W U X T2 hs fl) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=before q b hb hbq V W U X hs)
      (fun v => v=after q b hb hbq V W U X hs) (533*((X.length+1)*(q+b+1))) := by
  obtain ⟨_,_,_,_,ht,hw⟩ := CountedLateRepairInverse.lengths q b hb hbq V W U X hV hW hU
  exact placed_exact place _ _ _ _ (active_working _ _ _ _ _ _ _)
    (active_working _ _ _ _ _ _ _) (extra_working _ _ _ _ _ _ _ _)
    (CountedIdealToggle.runs (a := 1) q b hb hbq
      (CountedLateRepairInverse.temp q b hb hbq V W U X) X
      (CountedLateRepairInverse.target q b hb hbq V W U X)
      (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 hs
      (hw.trans hW) (ht.trans hV) hv hc rfl rfl rfl rfl)

end
end IntegerMultBounds.Machine.CountedLateRepairToggle
