import IntegerMultBounds.Machine.CountedLateRepairKeyCleanup
import IntegerMultBounds.Machine.CountedLateRankEndpoint

/-! The complete original-header late key machine on fixed34 tapes.
An actual short rank counter is split; the original address is classified,
its inverse and ideal destination are computed, and all generated work is erased. -/
namespace IntegerMultBounds.Machine.CountedLateRepairKeyRun
noncomputable section
open CountedLateRepairKeyBank
open CountedRankSplitBank (placed_exact)

def V (q : ℕ) (X cs : List Bool) := Gather.field cs 0 (X.length*q)
def W (q b : ℕ) (X cs : List Bool) := Gather.field cs (X.length*q) (X.length*b)
def U (q b : ℕ) (X cs : List Bool) := Gather.field cs (X.length*q+X.length*b) (X.length*b)

def rankPlace : Fin (13+21) ≃ Fin 34 where
  toFun := ![30,0,1,11,12,13,14,15,16,17,18,19,2,3,4,5,6,7,8,9,10,20,21,22,23,24,25,26,27,28,29,31,32,33]
  invFun := ![1,2,12,13,14,15,16,17,18,19,20,3,4,5,6,7,8,9,10,11,21,22,23,24,25,26,27,28,29,30,0,31,32,33]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rankProgram := Placement.placed (CountedLateRankRun.program (a := 1)) rankPlace

theorem rank_input (X cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active rankPlace (initial X cs hs)=CountedLateRankBank.bank (RepairScan.ctrTape cs)
      (fun _ => blank) (fun _ => blank) (fun _ => blank) 1 0 0 0 hs none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rank_output (q b : ℕ) (X cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active rankPlace (ranked (V q X cs) (W q b X cs) (U q b X cs) X cs hs)=
      CountedLateRankBank.bank (RepairScan.ctrTape cs)
        (CountedGuardGadgetRecord.word (V q X cs)) (CountedGuardGadgetRecord.word (W q b X cs))
        (CountedGuardGadgetRecord.word (U q b X cs)) 1 0 0 0 hs none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem extra_index (i : Fin 21) : rankPlace (Fin.natAdd 13 i)=![3,4,5,6,7,8,9,10,20,21,22,23,24,25,26,27,28,29,31,32,33] i := by
  fin_cases i <;> decide

theorem rank_extra (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.extra rankPlace (initial X cs hs)=Placement.extra rankPlace (ranked V W U X cs hs) := by
  unfold Placement.extra
  apply congrArg₂ Tapes.mk <;> funext i <;> rw [extra_index]
  all_goals fin_cases i <;> rfl

theorem rank_runs (q b : ℕ) (hq : 0<q) (hb : 0<b) (X cs : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime rankProgram (fun v => v=initial X cs hs)
      (fun v => v=ranked (V q X cs) (W q b X cs) (U q b X cs) X cs hs)
      (600*((X.length+1)*(q+b+1))) := by
  exact placed_exact rankPlace _ _ _ _ (rank_input X cs hs) (rank_output q b X cs hs)
    (rank_extra _ _ _ _ _ _) (CountedLateRankEndpoint.runs_linear
      (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 cs hs q b X.length hq hb hv hc)

def program := seq (seq rankProgram CountedLateRepairKeyWrite.program) CountedLateRepairKeyCleanup.program

def output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (X cs : List Bool) (hs : Fin 3 → List Bool) :=
  CountedLateRepairKeyCleanup.output q b hb hbq (V q X cs) (W q b X cs) (U q b X cs) X cs hs

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (X cs : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=initial X cs hs) (fun v => v=output q b hb hbq X cs hs)
      (10300*((X.length+1)*(q+b+1))) := by
  have hV : (V q X cs).length=X.length*q := Gather.field_length _ _ _
  have hW : (W q b X cs).length=X.length*b := Gather.field_length _ _ _
  have hU : (U q b X cs).length=X.length*b := Gather.field_length _ _ _
  have h1 := rank_runs q b (by omega) (by omega) X cs hs hv hc
  have h2 := CountedLateRepairKeyWrite.all_runs q b hb hbq hbq3
    (V q X cs) (W q b X cs) (U q b X cs) X cs hs hV hW hU hv hc
  have h3 := CountedLateRepairKeyCleanup.runs q b hb hbq
    (V q X cs) (W q b X cs) (U q b X cs) X cs hs hV hW hU
  refine ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) ?_
  have hp : 1≤(X.length+1)*(q+b+1) :=
    Nat.mul_pos (by omega : 0<X.length+1) (by omega : 0<q+b+1)
  omega

end
end IntegerMultBounds.Machine.CountedLateRepairKeyRun
