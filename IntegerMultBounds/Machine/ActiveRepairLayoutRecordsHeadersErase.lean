import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersCount

/-! Actual post-use erasure of all five generated repair/format descriptors.
The fourteen original headers survive, and every auxiliary tape is blank. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersErase
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairRankHeadersCommands
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsHeadersSchedule
open ActiveRepairLayoutRecordsHeadersCount
variable {s : Shape} {p : Parameters s} {offset rows a : ℕ}

def schedule : List Command := [.erase 14,.erase 16,.erase 17,.erase 18,.erase 19]
def program := (compile (a := a) schedule).snd
def runtime (d : Inputs s p offset rows) := scheduleCost schedule (ready d)

theorem runs (d : Inputs s p offset rows) :
    HoareTime (ActiveRepairLayoutRecordsHeadersErase.program (a := a)) (fun v => v=bank (ready d))
      (fun v => v=bank (initial d)) (runtime d) := by
  have hv : validSchedule schedule (ready d) := by
    simp [schedule,validSchedule,ActiveRepairRankHeadersCommands.valid,eval,ready,finished,scanned,put,Function.update]
  have he : execute schedule (ready d)=initial d := by
    funext i
    fin_cases i <;> simp [schedule,execute,eval,ready,finished,scanned,put,Function.update,initial]
  have h := schedule_runs (a := a) schedule (ready d) hv
  rwa [he] at h

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersErase
