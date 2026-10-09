import IntegerMultBounds.Machine.CompactChildHeadersArithmetic
import IntegerMultBounds.Machine.ActivePrefixStageHeadersRun

/-! Sparse phase stride, count and full-address offset are physically derived
from original node/global headers and the controller's current axis header.
The two arithmetic temporaries are blank again at the endpoint. -/
namespace IntegerMultBounds.Machine.SparsePhaseHeadersData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put)
variable {s : Shape} {a : ℕ}

def offset (v : Stage s) (axis : Fin v.f) (m : ℕ) :=
  s.H+s.B+(s.active-(v.left+(m-1)*v.f+axis.val)-1)*s.chunk+v.rho
def values (v : Stage s) (axis : Fin v.f) (m : ℕ) : Fin 3 → ℕ :=
  ![v.f*s.chunk,m-1,offset v axis m]
def initial (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) : State :=
  put (ActivePrefixStageHeadersData.finished order v rows) 25 axis.val
def finished (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) : State :=
  put (put (put (initial order v rows axis) 22 (values v axis m 0)) 23 (values v axis m 1))
    24 (values v axis m 2)

def schedule (m : ℕ) : List CompactChildHeadersArithmetic.Op :=
  [.constant 23 (m-1),
   .existing (.product ![7,23,26] (by decide)),
   .existing (.command (.copy 8 27 (by decide))),
   .existing (.command (.add 27 26 (by decide))),
   .existing (.command (.erase 26)),
   .existing (.command (.add 27 25 (by decide))),
   .constant 26 1,
   .existing (.command (.add 27 26 (by decide))),
   .existing (.command (.erase 26)),
   .existing (.command (.difference 3 27 26 (by decide))),
   .existing (.command (.erase 27)),
   .existing (.product ![0,26,24] (by decide)),
   .existing (.command (.erase 26)),
   .existing (.command (.add 24 10 (by decide))),
   .existing (.command (.add 24 13 (by decide))),
   .existing (.command (.add 24 14 (by decide))),
   .existing (.product ![0,7,22] (by decide))]

theorem last_fits (v : Stage s) (axis : Fin v.f) (m : ℕ) (hm : 0<m) (hslots : m≤v.slots) :
    v.left+(m-1)*v.f+axis.val+1≤s.active := by
  have hprod := Nat.mul_le_mul_right v.f hslots
  have hmf : (m-1)*v.f+v.f=m*v.f := by
    have h : m-1+1=m := by omega
    have hh := congrArg (fun n => n*v.f) h
    simpa only [Nat.add_mul,Nat.one_mul] using hh
  have hs := v.activeAxes
  have ha := axis.isLt
  omega

theorem execute_eq (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) :
    execute (schedule m) (initial order v rows axis)=finished order v rows axis m := by
  have hsub : s.active-(v.left+(m-1)*v.f+axis.val)-1=
      s.active-(v.left+(m-1)*v.f+axis.val+1) := by omega
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,finished,values,offset,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,Function.update]
  rw [hsub]
  omega

theorem schedule_valid (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (hm : 0<m) (hslots : m≤v.slots) :
    validSchedule (schedule m) (initial order v rows axis) := by
  have hf := v.positiveWidth
  have hq : 0<s.chunk := by have := v.selectedFits; omega
  have hfit := last_fits v axis m hm hslots
  simpa [schedule,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,initial,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,Function.update,hf,hq] using hfit

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (hm : 0<m) (hslots : m≤v.slots) :
    HoareTime (compile (a := a) (schedule m)).2
      (fun z => z=ActiveRepairRankHeadersCommands.bank (initial order v rows axis))
      (fun z => z=ActiveRepairRankHeadersCommands.bank (finished order v rows axis m))
      (scheduleCost (schedule m) (initial order v rows axis)) := by
  have h := schedule_runs (a := a) (schedule m) (initial order v rows axis)
    (schedule_valid order v rows axis m hm hslots)
  rw [execute_eq] at h
  exact h

end
end IntegerMultBounds.Machine.SparsePhaseHeadersData
