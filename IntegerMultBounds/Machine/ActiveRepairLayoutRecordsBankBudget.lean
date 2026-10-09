import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankPlaced
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersErase
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersBudget

/-! The real original-header consumer installation and the final generated
header erasure both have paid linear original payload-volume contracts. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersBudget
open ActiveRepairLayoutRecordsHeadersSchedule ActiveRepairLayoutRecordsHeadersCount
open ActiveRepairRankHeadersCommands
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem prepares_linear (d : Inputs s p offset rows) (rs : List Partition.Record)
    (hrows : 0<rows) (hp : 0<s.payload) (hfit : offset+p.f*p.q≤p.before) :
    HoareTime ActiveRepairLayoutRecordsBankPlaced.prepareProgram
      (fun v => v=ActiveRepairLayoutRecordsBankPlaced.originalInput d rs)
      (fun v => v=ActiveRepairLayoutRecordsBankPlaced.output d rs)
      ((constant+451)*volume s rows) := by
  apply (ActiveRepairLayoutRecordsBankPlaced.prepares d rs).consequence (fun _ h => h) (fun _ h => h)
  exact copies_runtime_linear d hrows hp hfit

theorem ready_bound (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.before) : Bounded (ready d) (2*volume s rows+1) := by
  intro i
  have hh := counted_bound d hrows hp hfit i
  fin_cases i
  all_goals first | exact hh | (change 0≤_; omega)

def eraseConstant := 4*(300*3^ActiveRepairLayoutRecordsHeadersErase.schedule.length)

theorem erase_runtime_linear (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.before) :
    ActiveRepairLayoutRecordsHeadersErase.runtime d≤eraseConstant*volume s rows := by
  have hv : 0<volume s rows := by unfold volume Shape.recordWidth; positivity
  have hh := scheduleCost_bounded ActiveRepairLayoutRecordsHeadersErase.schedule (ready d)
    (2*volume s rows+1) (ready_bound d hrows hp hfit)
  unfold ActiveRepairLayoutRecordsHeadersErase.runtime eraseConstant
  nlinarith

theorem erase_runs_linear {a : ℕ} (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.before) :
    HoareTime (ActiveRepairLayoutRecordsHeadersErase.program (a := a))
      (fun v => v=bank (ready d)) (fun v => v=ActiveRepairLayoutRecordsHeadersRun.originalInput d)
      (eraseConstant*volume s rows) := by
  have hh := ActiveRepairLayoutRecordsHeadersErase.runs (a := a) d
  rw [ActiveRepairLayoutRecordsHeadersRun.input_eq] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (erase_runtime_linear d hrows hp hfit)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankBudget
