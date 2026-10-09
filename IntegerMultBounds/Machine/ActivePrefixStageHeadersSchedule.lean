import IntegerMultBounds.Machine.ActivePrefixStageHeadersData

namespace IntegerMultBounds.Machine.ActivePrefixStageHeadersSchedule
open ActivePrefixStageHeadersData ActivePrefixStageHeadersOps
open ActiveRepairRankHeadersCommands (put)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry

 theorem execute_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ)
    (hG : 1≤s.guard) : execute (schedule order) (initial v rows)=finished order v rows := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  cases order <;> funext i <;> fin_cases i
  all_goals simp [schedule,seed,back,front,widths,highTarget,lowTarget,source,execute,eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,originalValues,Function.update,
    finished,outputs,offset,before,after,highAxes,lowAxes,earlyOffset,lateOffset,slotLow,
    CompactGadgetReservationShape.Shape.H,CompactGadgetReservationCapacity.capacity,
    Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  all_goals omega

def Ordered {s : Shape} (order : Order) (v : Stage s) : Prop :=
  match order with | .early => v.source.val<v.target.val | .late => v.target.val<v.source.val

theorem schedule_valid {s : Shape} (order : Order) (v : Stage s) (rows : ℕ)
    (hG : 1≤s.guard) (horder : Ordered order v) :
    validSchedule (schedule order) (initial v rows) := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  have hs := v.source.isLt
  have ht := v.target.isLt
  have hd := positive_axes v
  have hw := v.positiveWidth
  have hr := v.selectedFits
  change 0<s.axes*s.guard at hH
  cases order
  all_goals simp [Ordered] at horder
  all_goals simp [schedule,seed,back,front,widths,highTarget,lowTarget,source,validSchedule,valid,eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,initial,
    originalValues,Function.update,CompactGadgetReservationShape.Shape.H,
    CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  all_goals omega

end IntegerMultBounds.Machine.ActivePrefixStageHeadersSchedule
