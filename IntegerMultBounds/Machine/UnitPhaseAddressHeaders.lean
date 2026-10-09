import IntegerMultBounds.Machine.UnitPhaseStreamLoop

/-! Derive the complete global address width from original geometric headers
and the already-paid H/B/F stage headers. This width is produced on actual
header22; it is not supplied as a numeric descriptor by the final caller. -/
namespace IntegerMultBounds.Machine.UnitPhaseAddressHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put bank)
variable {s : Shape} {a : ℕ}

def initial (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) : State :=
  SparsePhaseHeadersData.initial order v rows axis
def finished (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) : State :=
  put (initial order v rows axis) 22 s.bits
def schedule : List Op :=
  [.existing (.product ![0,3,22] (by decide)),
   .existing (.command (.add 22 13 (by decide))),
   .existing (.command (.add 22 13 (by decide))),
   .existing (.command (.add 22 13 (by decide))),
   .existing (.command (.add 22 14 (by decide))),
   .existing (.command (.add 22 15 (by decide)))]
def program := (compile (a := a) schedule).2

theorem valid (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    validSchedule schedule (initial order v rows axis) := by
  have hq : 0<s.chunk := by have := v.selectedFits; omega
  simp [schedule,validSchedule,CompactChildHeadersArithmetic.valid,eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    initial,SparsePhaseHeadersData.initial,ActivePrefixStageHeadersData.finished,
    ActivePrefixStageHeadersData.originalValues,ActivePrefixStageHeadersData.outputs,put,Function.update,hq]

theorem execute_eq (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    execute schedule (initial order v rows axis)=finished order v rows axis := by
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,initial,finished,SparsePhaseHeadersData.initial,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,put,Function.update,Shape.bits]
  ring

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    HoareTime (program (a := a)) (fun z => z=bank (initial order v rows axis))
      (fun z => z=bank (finished order v rows axis)) (scheduleCost schedule (initial order v rows axis)) := by
  simpa only [program,execute_eq] using schedule_runs (a := a) schedule
    (initial order v rows axis) (valid order v rows axis)

end
end IntegerMultBounds.Machine.UnitPhaseAddressHeaders
