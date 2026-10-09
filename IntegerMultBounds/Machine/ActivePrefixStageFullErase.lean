import IntegerMultBounds.Machine.ActivePrefixStageFullData

/-! Paid physical erasure of every copied consumer descriptor after the full
stage. The original thirteen words and transformed raw array survive. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageFullErase
noncomputable section
open ActivePrefixStageFullData
open ActivePrefixStageHeadersRouting
open ActivePrefixStageHeadersData (Order)
open CompactGadgetReservationShape (Shape)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

def schedule : List Command := [.erase 43,.erase 44,.erase 45,.erase 46,.erase 47,
  .erase 48,.erase 49,.erase 50,.erase 51,.erase 52,.erase 53,.erase 54,.erase 55,
  .erase 56,.erase 57,.erase 58,.erase 59,.erase 60,.erase 61,.erase 62,.erase 63,.erase 64]
def program := (compile (a := prime) schedule).2
def cost (order : Order) (d : Inputs s) := scheduleCost schedule
  (ActivePrefixStageHeadersPlaced.finished order d.stage d.rows)

theorem execute_eq (order : Order) (d : Inputs s) :
    execute schedule (ActivePrefixStageHeadersPlaced.finished order d.stage d.rows)=
      ActivePrefixStageHeadersPlaced.lift (ActivePrefixStageHeadersData.initial d.stage d.rows) := by
  funext i; fin_cases i
  all_goals simp [schedule,execute,eval,ActivePrefixStageHeadersPlaced.finished,
    ActivePrefixStageHeadersPlaced.lift,ActivePrefixStageHeadersData.initial,
    ActivePrefixStageHeadersData.originalValues,Function.update]

theorem valid (order : Order) (d : Inputs s) :
    validSchedule schedule (ActivePrefixStageHeadersPlaced.finished order d.stage d.rows) := by
  simp [schedule,validSchedule,ActivePrefixStageHeadersRouting.valid,eval,
    ActivePrefixStageHeadersPlaced.finished,ActivePrefixStageHeadersData.finished,
    ActivePrefixStageHeadersPlaced.consumerSources,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,Function.update]

theorem runs (order : Order) (d : Inputs s) (x : ActiveRepairLayoutRecordsData.Array s d.rows) :
    HoareTime (extend program 1) (fun v => v=ready order d x)
      (fun v => v=original d x) (cost order d) := by
  have h := schedule_runs (a := prime) schedule
    (ActivePrefixStageHeadersPlaced.finished order d.stage d.rows) (valid order d)
  rw [execute_eq] at h
  exact hoare_extend_eq h (rawBank d x)

theorem bound (order : Order) (d : Inputs s) (horder : ActivePrefixStageHeadersSchedule.Ordered order d.stage) :
    cost order d≤5000*(d.rows*s.recordWidth) := by
  obtain ⟨ho,hv⟩ := ActivePrefixStageHeadersBudget.original_bounds order d.stage d.rows
    d.hG d.hGK horder d.hr d.hrecord
  have hb : ActivePrefixStageHeadersBudget.RoutingBounded
      (ActivePrefixStageHeadersPlaced.finished order d.stage d.rows) (d.rows*s.recordWidth) := by
    have hsource := ActivePrefixStageHeadersBudget.lift_finished_bounded order d.stage d.rows
      (d.rows*s.recordWidth) ho hv
    intro i
    by_cases h13 : i.val<13
    · simpa only [ActivePrefixStageHeadersPlaced.finished,h13,↓reduceDIte,Option.getD_some] using ho ⟨i.val,h13⟩
    · by_cases h43 : 43 ≤ i.val
      · let src := ActivePrefixStageHeadersPlaced.consumerSources ⟨i.val-43,by omega⟩
        have hh := hsource (Fin.castAdd 37 src)
        have hs : src.val<28 := src.isLt
        simpa only [ActivePrefixStageHeadersPlaced.finished,h13,h43,↓reduceDIte,
          ActivePrefixStageHeadersPlaced.lift,Fin.val_castAdd,hs] using hh
      · simp [ActivePrefixStageHeadersPlaced.finished,h13,h43]
  have h := ActivePrefixStageHeadersBudget.routing_cost_bound schedule
    (ActivePrefixStageHeadersPlaced.finished order d.stage d.rows) (d.rows*s.recordWidth) hb
  have hlen : schedule.length=22 := rfl
  rw [hlen] at h
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hpv : 0<s.recordWidth := by unfold Shape.recordWidth; positivity
  have hvolume := Nat.mul_pos d.hr hpv
  unfold cost
  omega

end
end IntegerMultBounds.Machine.ActivePrefixStageFullErase
