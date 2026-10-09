import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersData
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersLength

/-! A fixed retained-descriptor arithmetic schedule constructs n+1, full
source width and complete record address width from original early headers. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersSchedule
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairRankHeadersCommands
open ActiveRepairLayoutRecordsHeadersData
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def initial (_d : Inputs s p offset rows) : State := fun i =>
  if h : i.val<14 then some (ActivePrefixLayoutHeadersData.originalValues
    (ActivePrefixLayoutHeadersGeometry.inputs s p offset rows) ⟨i.val,h⟩) else none
def scanned (d : Inputs s p offset rows) := put (initial d) 14 (rowBits d)
def seeded (d : Inputs s p offset rows) := put (scanned d) 15 1
def finished (d : Inputs s p offset rows) :=
  put (put (put (scanned d) 16 (p.n+1)) 17 (p.n*p.q+p.q)) 18 (s.bits+rowBits d)

def schedule : List Command :=
  [.copy 9 16 (by decide),.add 16 15 (by decide),
   .copy 5 17 (by decide),.add 17 7 (by decide),
   .copy 0 18 (by decide),.add 18 0 (by decide),.add 18 0 (by decide),
   .add 18 1 (by decide),.add 18 2 (by decide),.add 18 3 (by decide),
   .add 18 4 (by decide),.add 18 5 (by decide),.add 18 14 (by decide),.erase 15]

theorem schedule_valid (d : Inputs s p offset rows) : validSchedule schedule (seeded d) := by
  simp [schedule,validSchedule,ActiveRepairRankHeadersCommands.valid,eval,seeded,scanned,initial,put,Function.update,
    ActivePrefixLayoutHeadersData.originalValues,ActivePrefixLayoutHeadersGeometry.inputs]

theorem execute_eq (d : Inputs s p offset rows) : execute schedule (seeded d)=finished d := by
  have ha := p.activeSize
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,seeded,scanned,initial,put,Function.update,finished,
    ActivePrefixLayoutHeadersData.originalValues,ActivePrefixLayoutHeadersGeometry.inputs,Shape.bits]
  omega

def program {a : ℕ} := (compile (a := a) schedule).2

theorem runs {a : ℕ} (d : Inputs s p offset rows) :
    HoareTime (program (a := a)) (fun v => v=bank (seeded d))
      (fun v => v=bank (finished d)) (scheduleCost schedule (seeded d)) := by
  have hh := schedule_runs (a := a) schedule (seeded d) (schedule_valid d)
  rwa [execute_eq] at hh

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersSchedule
