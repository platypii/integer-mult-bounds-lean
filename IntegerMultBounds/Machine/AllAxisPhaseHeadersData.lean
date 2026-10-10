import IntegerMultBounds.Machine.SparsePhaseHeadersData

/-! One all-axis sparse control stream: stride is the chunk width, count is
residual dimension times runtime axis width, and offset starts at the lowest
address bit of the last residual slot. Descriptors are synthesized physically
from original headers, with both arithmetic temporaries restored. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseHeadersData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put)
variable {s : Shape} {a : ℕ}

def offset (v : Stage s) (m : ℕ) := s.H+s.B+(s.active-(v.left+m*v.f))*s.chunk+v.rho
def values (v : Stage s) (m : ℕ) : Fin 3 → ℕ := ![s.chunk,m*v.f-1,offset v m]
def initial (order : Order) (v : Stage s) (rows : ℕ) := ActivePrefixStageHeadersData.finished order v rows
def finished (order : Order) (v : Stage s) (rows m : ℕ) : State :=
  put (put (put (initial order v rows) 22 (values v m 0)) 23 (values v m 1)) 24 (values v m 2)

def schedule (m : ℕ) : List CompactChildHeadersArithmetic.Op :=
  [.constant 23 m,
   .existing (.product ![7,23,26] (by decide)),
   .existing (.command (.erase 23)),
   .constant 27 1,
   .existing (.command (.difference 26 27 23 (by decide))),
   .existing (.command (.erase 27)),
   .existing (.command (.copy 8 27 (by decide))),
   .existing (.command (.add 27 26 (by decide))),
   .existing (.command (.erase 26)),
   .existing (.command (.difference 3 27 26 (by decide))),
   .existing (.command (.erase 27)),
   .existing (.product ![0,26,24] (by decide)),
   .existing (.command (.erase 26)),
   .existing (.command (.add 24 10 (by decide))),
   .existing (.command (.add 24 13 (by decide))),
   .existing (.command (.add 24 14 (by decide))),
   .existing (.command (.copy 0 22 (by decide)))]

theorem fits (v : Stage s) (m : ℕ) (hslots : m≤v.slots) : v.left+m*v.f≤s.active := by
  have hm := Nat.mul_le_mul_right v.f hslots
  have hs := v.activeAxes
  omega

theorem execute_eq (order : Order) (v : Stage s) (rows m : ℕ) :
    execute (schedule m) (initial order v rows)=finished order v rows m := by
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,finished,values,offset,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,Function.update,Nat.mul_comm]
  ring

theorem schedule_valid (order : Order) (v : Stage s) (rows m : ℕ)
    (hm : 0<m) (hslots : m≤v.slots) : validSchedule (schedule m) (initial order v rows) := by
  have hf := v.positiveWidth
  have hq : 0<s.chunk := by have := v.selectedFits; omega
  have hfit := fits v m hslots
  have hprod : 0<m*v.f := Nat.mul_pos hm hf
  simp [schedule,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,initial,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,Function.update,Nat.mul_comm,hf,hq,hfit]
  omega

theorem runs (order : Order) (v : Stage s) (rows m : ℕ)
    (hm : 0<m) (hslots : m≤v.slots) :
    HoareTime (compile (a := a) (schedule m)).2
      (fun z => z=ActiveRepairRankHeadersCommands.bank (initial order v rows))
      (fun z => z=ActiveRepairRankHeadersCommands.bank (finished order v rows m))
      (scheduleCost (schedule m) (initial order v rows)) := by
  have hr := schedule_runs (a := a) (schedule m) (initial order v rows)
    (schedule_valid order v rows m hm hslots)
  rw [execute_eq] at hr
  exact hr

end
end IntegerMultBounds.Machine.AllAxisPhaseHeadersData
