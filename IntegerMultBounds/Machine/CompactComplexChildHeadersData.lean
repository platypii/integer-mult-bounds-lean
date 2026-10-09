import IntegerMultBounds.Machine.ActivePrefixStageHeadersData
import IntegerMultBounds.Machine.CompactChildHeadersArithmetic
import IntegerMultBounds.Machine.CompactComplexRecursiveGeometry

/-! Paid child-node header arithmetic for an internal child. The row count
belongs to the already selected role stream and is retained. -/
namespace IntegerMultBounds.Machine.CompactComplexChildHeadersData
noncomputable section
open CompactChildHeadersArithmetic
open CompactComplexRecursiveGeometry
open CompactBinaryBasisSchedule
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageHeadersData (initial)
open Networks.BinaryRowProgram (Op)

def schedule (slot : Fin arity) : List CompactChildHeadersArithmetic.Op :=
  [.constant 22 slot.val,
   .existing (.product ![7,22,23] (by decide)),
   .existing (.command (.copy 8 24 (by decide))),
   .existing (.command (.add 24 23 (by decide))),
   .existing (.command (.erase 23)),
   .quotient ![7,6,25] (by decide),
   .existing (.product ![6,25,26] (by decide)),
   .existing (.command (.add 26 24 (by decide))),
   .existing (.command (.difference 3 26 27 (by decide))),
   .existing (.command (.erase 7)),.existing (.command (.copy 25 7 (by decide))),
   .existing (.command (.erase 8)),.existing (.command (.copy 24 8 (by decide))),
   .existing (.command (.erase 9)),.existing (.command (.copy 27 9 (by decide))),
   .existing (.command (.erase 22)),.existing (.command (.erase 24)),
   .existing (.command (.erase 25)),.existing (.command (.erase 26)),
   .existing (.command (.erase 27))]

variable {s : Shape} (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+2)) (hactive : s.active ≤ s.axes)
    (pair : Op (Fin arity)) (slot : Fin arity) (rows : ℕ)

def parent := stage (node rho visit hactive) pair

def child := stage (node rho (Visit.child visit slot) hactive) pair

theorem execute_eq : execute (schedule slot) (initial (parent rho visit hactive pair) rows) =
    initial (child rho visit hactive pair slot) rows := by
  have hp : 0 < arity := by decide
  have hdiv : arity^(k+1) / arity = arity^k := by
    rw [pow_succ, Nat.mul_div_cancel _ hp]
  have hpow : arity^(k+1) = arity*arity^k := by rw [pow_succ,Nat.mul_comm]
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,
    ActivePrefixStageHeadersData.originalValues,parent,child,stage,node,
    Function.update,hdiv]
  all_goals rw [hpow]
  rw [Nat.mul_comm (arity^k) arity, Nat.add_comm (arity*arity^k)]


theorem schedule_valid : validSchedule (schedule slot) (initial (parent rho visit hactive pair) rows) := by
  have hp : 0 < arity := by decide
  have hfp : 0 < arity^(k+1) := pow_pos hp _
  have hdiv : arity^(k+1) / arity = arity^k := by
    rw [pow_succ, Nat.mul_div_cancel _ hp]
  have hfit := (Visit.child visit slot).fits
  simp [schedule,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,
    ActivePrefixStageHeadersData.originalValues,parent,stage,node,Function.update,hdiv,hp,hfp]
  rw [← pow_succ]
  simpa only [Nat.add_comm] using hfit

variable {a : ℕ}

theorem runs : HoareTime (compile (a := a) (schedule slot)).2
    (fun x => x = ActiveRepairRankHeadersCommands.bank (initial (parent rho visit hactive pair) rows))
    (fun x => x = ActiveRepairRankHeadersCommands.bank (initial (child rho visit hactive pair slot) rows))
    (scheduleCost (schedule slot) (initial (parent rho visit hactive pair) rows)) := by
  have h := schedule_runs (a := a) (schedule slot) (initial (parent rho visit hactive pair) rows)
    (schedule_valid rho visit hactive pair slot rows)
  rw [execute_eq] at h
  exact h


/-- The original sixty-six-tape caller retains every trailing tape, including
its raw role payload and descriptor/return stacks. -/
def placedProgram (slot : Fin arity) := extend (compile (a := a) (schedule slot)).2 23

theorem runs_framed (tail : Tapes 23 a) : HoareTime (placedProgram (a := a) slot)
    (fun x => x = (ActiveRepairRankHeadersCommands.bank
      (initial (parent rho visit hactive pair) rows)).append tail)
    (fun x => x = (ActiveRepairRankHeadersCommands.bank
      (initial (child rho visit hactive pair slot) rows)).append tail)
    (scheduleCost (schedule slot) (initial (parent rho visit hactive pair) rows)) :=
  hoare_extend_eq (runs rho visit hactive pair slot rows) tail

end
end IntegerMultBounds.Machine.CompactComplexChildHeadersData
