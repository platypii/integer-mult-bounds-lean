import IntegerMultBounds.Machine.UnitPhaseCountPower

/-! Derive the complete coefficient count rows*2^bits from original rows4
and derived width22. Power23 is constructed from tape, multiplied with rows,
then erased; generated count24 remains and original rows4 is retained. -/
namespace IntegerMultBounds.Machine.UnitPhaseCountHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put bank)
variable {s : Shape}

def powerState (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) : State :=
  put (UnitPhaseAddressHeaders.finished order v rows axis) 23 (2^s.bits)
def finished (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) : State :=
  put (UnitPhaseAddressHeaders.finished order v rows axis) 24 (rows*2^s.bits)
def schedule : List Op :=
  [.existing (.product ![23,4,24] (by decide)),.existing (.command (.erase 23))]
def arithmetic := (compile (a := 2) schedule).2
def program := seq UnitPhaseCountPower.program arithmetic

def cost (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :=
  FixedBasePowerDescriptor.constant 2*2^s.bits+scheduleCost schedule (powerState order v rows axis)+1

private theorem bank_power (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    bank (a := 2) (powerState order v rows axis)=UnitPhaseCountPower.output order v rows axis := by
  change (ActiveRepairRankHeadersCommands.caller (a := 2) (put _ 23 _)).append (SharedBank.empty 15 2)=_
  rw [ActiveRepairRankHeadersCommands.put_caller]
  exact (SharedPlacementAlphabet.setTape_append_left _ _ (23 : Fin 28) _ _).symm

theorem valid (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    validSchedule schedule (powerState order v rows axis) := by
  have hpow : 0<2^s.bits := by positivity
  simp [schedule,validSchedule,CompactChildHeadersArithmetic.valid,eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,
    powerState,UnitPhaseAddressHeaders.finished,UnitPhaseAddressHeaders.initial,SparsePhaseHeadersData.initial,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    put,Function.update,hpow]

theorem execute_eq (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    execute schedule (powerState order v rows axis)=finished order v rows axis := by
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,powerState,finished,UnitPhaseAddressHeaders.finished,
    UnitPhaseAddressHeaders.initial,SparsePhaseHeadersData.initial,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,put,Function.update]

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    HoareTime program (fun z => z=UnitPhaseCountPower.input order v rows axis)
      (fun z => z=bank (finished order v rows axis)) (cost order v rows axis) := by
  have h0 := UnitPhaseCountPower.runs order v rows axis
  have h1 := schedule_runs (a := 2) schedule (powerState order v rows axis) (valid order v rows axis)
  rw [bank_power,execute_eq] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.UnitPhaseCountHeaders
