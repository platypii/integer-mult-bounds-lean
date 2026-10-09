import IntegerMultBounds.Machine.ButterflyAxisHeadersArithmetic
import IntegerMultBounds.Machine.ButterflyGuard
import IntegerMultBounds.Machine.CompactRowHeaders

/-! Actual selected-axis header synthesis from original dimension D, selected
position t, polynomial multiplicity R and initial precision p. Signed coefficient
width, binary powers, row dimensions and paired-loop counts are physically
constructed by a fixed arithmetic schedule; no derived descriptor is preloaded. -/
namespace IntegerMultBounds.Machine.ButterflyAxisHeadersData
noncomputable section
open ButterflyAxisHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put)

abbrev cmd (c : ActiveRepairRankHeadersCommands.Command) : Op := .base (.existing (.command c))
abbrev product (f : Fin 3 → Fin 28) (hf : Function.Injective f) : Op := .base (.existing (.product f hf))

def schedule : List Op :=
  [.base (.constant 4 1),.base (.constant 5 2),.base (.constant 6 0),.base (.constant 20 4),
   cmd (.copy 0 19 (by decide)),cmd (.add 19 0 (by decide)),cmd (.add 19 3 (by decide)),cmd (.add 19 20 (by decide)),
   cmd (.difference 0 1 7 (by decide)),cmd (.difference 7 4 8 (by decide)),
   .power ![1,9] (by decide),.power ![8,10] (by decide),
   product ![2,9,11] (by decide),cmd (.copy 19 16 (by decide)),cmd (.add 16 4 (by decide)),
   product ![5,16,17] (by decide),product ![17,11,12] (by decide),
   product ![5,10,13] (by decide),product ![11,10,14] (by decide),product ![12,10,15] (by decide)]

def initial (D t R p : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with | 0 => some D | 1 => some t | 2 => some R | 3 => some p | _ => none

def higher (D t : ℕ) := 2^(D-t-1)
def lower (t R : ℕ) := 2^t*R
def width (D p : ℕ) := D+D+p+4
def recordLength (D p : ℕ) := (width D p+1)*2
def rowLength (D t R p : ℕ) := lower t R*recordLength D p
def pairCount (D t R : ℕ) := higher D t*lower t R
def streamLength (D t R p : ℕ) := higher D t*rowLength D t R p

def output (D t R p : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some D | 1 => some t | 2 => some R | 3 => some p
  | 4 => some 1 | 5 => some 2 | 6 => some 0
  | 7 => some (D-t) | 8 => some (D-t-1)
  | 9 => some (2^t) | 10 => some (higher D t)
  | 11 => some (lower t R) | 12 => some (rowLength D t R p)
  | 13 => some (higher D t*2) | 14 => some (pairCount D t R)
  | 15 => some (streamLength D t R p)
  | 16 => some (width D p+1) | 17 => some (recordLength D p)
  | 19 => some (width D p) | 20 => some 4 | _ => none

theorem execute_eq (D t R p : ℕ) : execute schedule (initial D t R p)=output D t R p := by
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,output,higher,lower,width,recordLength,rowLength,pairCount,
    streamLength,Function.update]

theorem valid (D t R p : ℕ) (ht : t<D) (hR : 0<R) : validSchedule schedule (initial D t R p) := by
  have hlow : 0<2^t*R := Nat.mul_pos (pow_pos (by decide) _) hR
  simp [schedule,validSchedule,ButterflyAxisHeadersArithmetic.valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,initial,Function.update]
  omega

theorem width_eq (D p : ℕ) : width D p=ButterflyGuard.width p D := by
  unfold width ButterflyGuard.width ButterflyGuard.halfWidth
  omega

variable {a : ℕ}

theorem runs (D t R p : ℕ) (ht : t<D) (hR : 0<R) :
    HoareTime (compile (a:=a) schedule).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D t R p))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (output D t R p))
      (scheduleCost schedule (initial D t R p)) := by
  have hh := schedule_runs (a:=a) schedule (initial D t R p) (valid D t R p ht hR)
  rw [execute_eq] at hh
  exact hh

end
end IntegerMultBounds.Machine.ButterflyAxisHeadersData
