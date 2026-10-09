import IntegerMultBounds.Machine.ButterflySpectatorGeometry
import IntegerMultBounds.Machine.ButterflyGuard
import IntegerMultBounds.Machine.CompactRowHeaders

/-! Actual selected-axis header synthesis from original dimension D, selected
position t, polynomial multiplicity R and initial precision p. Signed coefficient
width, binary powers, row dimensions and paired-loop counts are physically
constructed by a fixed arithmetic schedule; no derived descriptor is preloaded. -/
namespace IntegerMultBounds.Machine.ButterflySpectatorHeaders
noncomputable section
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product higher lower width recordLength rowLength pairCount streamLength)
open ActiveRepairRankHeadersCommands (State put)

def schedule : List Op :=
  [.base (.constant 4 1),.base (.constant 5 2),.base (.constant 6 0),.base (.constant 20 4),
   cmd (.copy 0 19 (by decide)),cmd (.add 19 0 (by decide)),cmd (.add 19 3 (by decide)),cmd (.add 19 20 (by decide)),
   cmd (.difference 0 1 7 (by decide)),cmd (.difference 7 4 8 (by decide)),
   .power ![1,9] (by decide),.power ![8,10] (by decide),
   product ![18,10,21] (by decide),cmd (.erase 10),cmd (.copy 21 10 (by decide)),cmd (.erase 21),
   product ![2,9,11] (by decide),cmd (.copy 19 16 (by decide)),cmd (.add 16 4 (by decide)),
   product ![5,16,17] (by decide),product ![17,11,12] (by decide),
   product ![5,10,13] (by decide),product ![11,10,14] (by decide),product ![12,10,15] (by decide)]

def initial (rows D t R p : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with | 0 => some D | 1 => some t | 2 => some R | 3 => some p | 18 => some rows | _ => none

def output (rows D t R p : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some D | 1 => some t | 2 => some R | 3 => some p
  | 4 => some 1 | 5 => some 2 | 6 => some 0
  | 7 => some (D-t) | 8 => some (D-t-1)
  | 9 => some (2^t) | 10 => some (rows*higher D t)
  | 11 => some (lower t R) | 12 => some (rowLength D t R p)
  | 13 => some (rows*higher D t*2) | 14 => some (rows*pairCount D t R)
  | 15 => some (rows*streamLength D t R p)
  | 16 => some (width D p+1) | 17 => some (recordLength D p)
  | 18 => some rows | 19 => some (width D p) | 20 => some 4 | _ => none

theorem execute_eq (rows D t R p : ℕ) : execute schedule (initial rows D t R p)=output rows D t R p := by
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,output,higher,lower,width,recordLength,rowLength,pairCount,
    streamLength,Function.update]
  all_goals ring

theorem valid (rows D t R p : ℕ) (ht : t<D) (hR : 0<R) (hr : 0<rows) : validSchedule schedule (initial rows D t R p) := by
  have hlow : 0<2^t*R := Nat.mul_pos (pow_pos (by decide) _) hR
  simp [schedule,validSchedule,ButterflyAxisHeadersArithmetic.valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,initial,Function.update]
  omega

variable {a : ℕ}

theorem runs (rows D t R p : ℕ) (ht : t<D) (hR : 0<R) (hr : 0<rows) :
    HoareTime (compile (a:=a) schedule).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial rows D t R p))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (output rows D t R p))
      (scheduleCost schedule (initial rows D t R p)) := by
  have hh := schedule_runs (a:=a) schedule (initial rows D t R p) (valid rows D t R p ht hR hr)
  rw [execute_eq] at hh
  exact hh


def cleanup : List Op := cmd (.add 1 4 (by decide))::
  ([4,5,6,7,8,9,10,11,12,13,14,15,16,17,19,20] : List (Fin 28)).map (fun i => cmd (.erase i))

theorem cleanup_eval (rows D t R p : ℕ) : execute cleanup (output rows D t R p)=initial rows D (t+1) R p := by
  funext i
  fin_cases i
  all_goals simp [cleanup,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,output,Function.update]

theorem cleanup_valid (rows D t R p : ℕ) : validSchedule cleanup (output rows D t R p) := by
  simp [cleanup,validSchedule,ButterflyAxisHeadersArithmetic.valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,output,Function.update]

theorem cleanup_runs (rows D t R p : ℕ) :
    HoareTime (compile (a:=a) cleanup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (output rows D t R p))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial rows D (t+1) R p))
      (scheduleCost cleanup (output rows D t R p)) := by
  have hh := schedule_runs (a:=a) cleanup _ (cleanup_valid rows D t R p)
  rwa [cleanup_eval] at hh

end
end IntegerMultBounds.Machine.ButterflySpectatorHeaders
