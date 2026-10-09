import IntegerMultBounds.Machine.ActivePrefixStageHeadersPlaced

namespace IntegerMultBounds.Machine.ActivePrefixStageHeadersBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActivePrefixStageHeadersData ActivePrefixStageHeadersSchedule

def intermediate {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) (slots : List (Fin 28)) : ActiveRepairRankHeadersCommands.State := fun i =>
  if i.val=22 then some 1 else if i∈slots then ActivePrefixStageHeadersData.finished order v rows i else initial v rows i

def seedSlots : List (Fin 28) := [13,20]
def backSlots := seedSlots++[14]
def frontSlots := backSlots++[15]
def widthSlots := frontSlots++[18,19]
def highSlots := widthSlots++[16]
def lowSlots := highSlots++[17]
def sourceSlots := lowSlots++[21]

theorem seed_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) :
    ActivePrefixStageHeadersOps.execute seed (initial v rows)=intermediate order v rows seedSlots := by
  funext i; fin_cases i
  all_goals simp [seed,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,originalValues,
    intermediate,seedSlots,finished,outputs,Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm]

theorem back_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard) :
    ActivePrefixStageHeadersOps.execute (back) (intermediate order v rows seedSlots)=intermediate order v rows backSlots := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  cases order <;> funext i <;> fin_cases i
  all_goals simp [back,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,originalValues,
    intermediate,seedSlots,backSlots,finished,outputs,offset,
    before,after,highAxes,lowAxes,earlyOffset,lateOffset,slotLow,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  all_goals omega

theorem front_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard) :
    ActivePrefixStageHeadersOps.execute (front) (intermediate order v rows backSlots)=intermediate order v rows frontSlots := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  cases order <;> funext i <;> fin_cases i
  all_goals simp [front,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,originalValues,
    intermediate,seedSlots,backSlots,frontSlots,finished,outputs,offset,
    before,after,highAxes,lowAxes,earlyOffset,lateOffset,slotLow,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  all_goals omega

theorem width_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard) :
    ActivePrefixStageHeadersOps.execute (widths) (intermediate order v rows frontSlots)=intermediate order v rows widthSlots := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  cases order <;> funext i <;> fin_cases i
  all_goals simp [widths,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.put,initial,originalValues,
    intermediate,seedSlots,backSlots,frontSlots,widthSlots,finished,outputs,offset,
    before,after,highAxes,lowAxes,earlyOffset,lateOffset,slotLow,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢


theorem high_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard) :
    ActivePrefixStageHeadersOps.execute (highTarget) (intermediate order v rows widthSlots)=intermediate order v rows highSlots := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  cases order <;> funext i <;> fin_cases i
  all_goals simp [highTarget,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,originalValues,
    intermediate,seedSlots,backSlots,frontSlots,widthSlots,highSlots,finished,outputs,offset,
    before,after,highAxes,lowAxes,earlyOffset,lateOffset,slotLow,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢


theorem low_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard) :
    ActivePrefixStageHeadersOps.execute (lowTarget) (intermediate order v rows highSlots)=intermediate order v rows lowSlots := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  cases order <;> funext i <;> fin_cases i
  all_goals simp [lowTarget,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,originalValues,
    intermediate,seedSlots,backSlots,frontSlots,widthSlots,highSlots,lowSlots,finished,outputs,offset,
    before,after,highAxes,lowAxes,earlyOffset,lateOffset,slotLow,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢


theorem source_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard) :
    ActivePrefixStageHeadersOps.execute (source order) (intermediate order v rows lowSlots)=intermediate order v rows sourceSlots := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  cases order <;> funext i <;> fin_cases i
  all_goals simp [source,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,originalValues,
    intermediate,seedSlots,backSlots,frontSlots,widthSlots,highSlots,lowSlots,sourceSlots,finished,outputs,offset,
    before,after,highAxes,lowAxes,earlyOffset,lateOffset,slotLow,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢


theorem seed_cost_bound {s : Shape} (order : Order) (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs order v i≤A) :
    ActivePrefixStageHeadersOps.scheduleCost (seed) (initial v rows)≤50000*(A+1) := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  have ho0 : s.chunk≤A := ho (0 : Fin 13)
  have ho1 : s.axes≤A := ho (1 : Fin 13)
  have ho2 : s.guard≤A := ho (2 : Fin 13)
  have ho3 : s.active≤A := ho (3 : Fin 13)
  have ho4 : rows≤A := ho (4 : Fin 13)
  have ho5 : s.payload≤A := ho (5 : Fin 13)
  have ho6 : v.slots≤A := ho (6 : Fin 13)
  have ho7 : v.f≤A := ho (7 : Fin 13)
  have ho8 : v.left≤A := ho (8 : Fin 13)
  have ho9 : v.right≤A := ho (9 : Fin 13)
  have ho10 : v.rho≤A := ho (10 : Fin 13)
  have ho11 : v.source.val≤A := ho (11 : Fin 13)
  have ho12 : v.target.val≤A := ho (12 : Fin 13)
  have hv0 : s.axes*s.guard≤A := hv (0 : Fin 9)
  have hv1 : s.B≤A := hv (1 : Fin 9)
  have hv2 : s.F≤A := hv (2 : Fin 9)
  have hv3 : before v≤A := hv (3 : Fin 9)
  have hv4 : after v≤A := hv (4 : Fin 9)
  have hv5 : (v.f-1)*s.chunk≤A := hv (5 : Fin 9)
  have hv6 : (v.f-1)*s.guard≤A := hv (6 : Fin 9)
  have hv7 : v.f-1≤A := hv (7 : Fin 9)
  have hv8 : offset order v≤A := hv (8 : Fin 9)
  simp only [Nat.mul_comm] at hv0 hv5 hv6
  simp [seed,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    initial,originalValues,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  omega

theorem back_cost_bound {s : Shape} (order : Order) (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs order v i≤A) :
    ActivePrefixStageHeadersOps.scheduleCost (back) (intermediate order v rows seedSlots)≤50000*(A+1) := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  have ho0 : s.chunk≤A := ho (0 : Fin 13)
  have ho1 : s.axes≤A := ho (1 : Fin 13)
  have ho2 : s.guard≤A := ho (2 : Fin 13)
  have ho3 : s.active≤A := ho (3 : Fin 13)
  have ho4 : rows≤A := ho (4 : Fin 13)
  have ho5 : s.payload≤A := ho (5 : Fin 13)
  have ho6 : v.slots≤A := ho (6 : Fin 13)
  have ho7 : v.f≤A := ho (7 : Fin 13)
  have ho8 : v.left≤A := ho (8 : Fin 13)
  have ho9 : v.right≤A := ho (9 : Fin 13)
  have ho10 : v.rho≤A := ho (10 : Fin 13)
  have ho11 : v.source.val≤A := ho (11 : Fin 13)
  have ho12 : v.target.val≤A := ho (12 : Fin 13)
  have hv0 : s.axes*s.guard≤A := hv (0 : Fin 9)
  have hv1 : s.B≤A := hv (1 : Fin 9)
  have hv2 : s.F≤A := hv (2 : Fin 9)
  have hv3 : before v≤A := hv (3 : Fin 9)
  have hv4 : after v≤A := hv (4 : Fin 9)
  have hv5 : (v.f-1)*s.chunk≤A := hv (5 : Fin 9)
  have hv6 : (v.f-1)*s.guard≤A := hv (6 : Fin 9)
  have hv7 : v.f-1≤A := hv (7 : Fin 9)
  have hv8 : offset order v≤A := hv (8 : Fin 9)
  simp only [Nat.mul_comm] at hv0 hv5 hv6
  simp [back,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    initial,originalValues,intermediate,seedSlots,
    finished,outputs,Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  omega

theorem front_cost_bound {s : Shape} (order : Order) (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs order v i≤A) :
    ActivePrefixStageHeadersOps.scheduleCost (front) (intermediate order v rows backSlots)≤50000*(A+1) := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  have ho0 : s.chunk≤A := ho (0 : Fin 13)
  have ho1 : s.axes≤A := ho (1 : Fin 13)
  have ho2 : s.guard≤A := ho (2 : Fin 13)
  have ho3 : s.active≤A := ho (3 : Fin 13)
  have ho4 : rows≤A := ho (4 : Fin 13)
  have ho5 : s.payload≤A := ho (5 : Fin 13)
  have ho6 : v.slots≤A := ho (6 : Fin 13)
  have ho7 : v.f≤A := ho (7 : Fin 13)
  have ho8 : v.left≤A := ho (8 : Fin 13)
  have ho9 : v.right≤A := ho (9 : Fin 13)
  have ho10 : v.rho≤A := ho (10 : Fin 13)
  have ho11 : v.source.val≤A := ho (11 : Fin 13)
  have ho12 : v.target.val≤A := ho (12 : Fin 13)
  have hv0 : s.axes*s.guard≤A := hv (0 : Fin 9)
  have hv1 : s.B≤A := hv (1 : Fin 9)
  have hv2 : s.F≤A := hv (2 : Fin 9)
  have hv3 : before v≤A := hv (3 : Fin 9)
  have hv4 : after v≤A := hv (4 : Fin 9)
  have hv5 : (v.f-1)*s.chunk≤A := hv (5 : Fin 9)
  have hv6 : (v.f-1)*s.guard≤A := hv (6 : Fin 9)
  have hv7 : v.f-1≤A := hv (7 : Fin 9)
  have hv8 : offset order v≤A := hv (8 : Fin 9)
  simp only [Nat.mul_comm] at hv0 hv5 hv6
  simp [front,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    initial,originalValues,intermediate,seedSlots,backSlots,
    finished,outputs,Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  omega

theorem widths_cost_bound {s : Shape} (order : Order) (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs order v i≤A) :
    ActivePrefixStageHeadersOps.scheduleCost (widths) (intermediate order v rows frontSlots)≤50000*(A+1) := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  have ho0 : s.chunk≤A := ho (0 : Fin 13)
  have ho1 : s.axes≤A := ho (1 : Fin 13)
  have ho2 : s.guard≤A := ho (2 : Fin 13)
  have ho3 : s.active≤A := ho (3 : Fin 13)
  have ho4 : rows≤A := ho (4 : Fin 13)
  have ho5 : s.payload≤A := ho (5 : Fin 13)
  have ho6 : v.slots≤A := ho (6 : Fin 13)
  have ho7 : v.f≤A := ho (7 : Fin 13)
  have ho8 : v.left≤A := ho (8 : Fin 13)
  have ho9 : v.right≤A := ho (9 : Fin 13)
  have ho10 : v.rho≤A := ho (10 : Fin 13)
  have ho11 : v.source.val≤A := ho (11 : Fin 13)
  have ho12 : v.target.val≤A := ho (12 : Fin 13)
  have hv0 : s.axes*s.guard≤A := hv (0 : Fin 9)
  have hv1 : s.B≤A := hv (1 : Fin 9)
  have hv2 : s.F≤A := hv (2 : Fin 9)
  have hv3 : before v≤A := hv (3 : Fin 9)
  have hv4 : after v≤A := hv (4 : Fin 9)
  have hv5 : (v.f-1)*s.chunk≤A := hv (5 : Fin 9)
  have hv6 : (v.f-1)*s.guard≤A := hv (6 : Fin 9)
  have hv7 : v.f-1≤A := hv (7 : Fin 9)
  have hv8 : offset order v≤A := hv (8 : Fin 9)
  simp only [Nat.mul_comm] at hv0 hv5 hv6
  simp [widths,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.put,
    initial,originalValues,intermediate,seedSlots,backSlots,frontSlots,
    finished,outputs,Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  omega

theorem highTarget_cost_bound {s : Shape} (order : Order) (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs order v i≤A) :
    ActivePrefixStageHeadersOps.scheduleCost (highTarget) (intermediate order v rows widthSlots)≤50000*(A+1) := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  have ho0 : s.chunk≤A := ho (0 : Fin 13)
  have ho1 : s.axes≤A := ho (1 : Fin 13)
  have ho2 : s.guard≤A := ho (2 : Fin 13)
  have ho3 : s.active≤A := ho (3 : Fin 13)
  have ho4 : rows≤A := ho (4 : Fin 13)
  have ho5 : s.payload≤A := ho (5 : Fin 13)
  have ho6 : v.slots≤A := ho (6 : Fin 13)
  have ho7 : v.f≤A := ho (7 : Fin 13)
  have ho8 : v.left≤A := ho (8 : Fin 13)
  have ho9 : v.right≤A := ho (9 : Fin 13)
  have ho10 : v.rho≤A := ho (10 : Fin 13)
  have ho11 : v.source.val≤A := ho (11 : Fin 13)
  have ho12 : v.target.val≤A := ho (12 : Fin 13)
  have hv0 : s.axes*s.guard≤A := hv (0 : Fin 9)
  have hv1 : s.B≤A := hv (1 : Fin 9)
  have hv2 : s.F≤A := hv (2 : Fin 9)
  have hv3 : before v≤A := hv (3 : Fin 9)
  have hv4 : after v≤A := hv (4 : Fin 9)
  have hv5 : (v.f-1)*s.chunk≤A := hv (5 : Fin 9)
  have hv6 : (v.f-1)*s.guard≤A := hv (6 : Fin 9)
  have hv7 : v.f-1≤A := hv (7 : Fin 9)
  have hv8 : offset order v≤A := hv (8 : Fin 9)
  simp only [Nat.mul_comm] at hv0 hv5 hv6
  have htm : v.target.val*v.f≤(v.target.val*v.f+v.left)*s.chunk :=
    (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _ hK)
  have hbase : (v.target.val*v.f+v.left)*s.chunk≤before v := by unfold before highAxes; rw [Nat.add_comm v.left]; omega
  have hdiff : s.chunk-v.rho≤A := (Nat.sub_le _ _).trans ho0
  simp only [Nat.mul_comm,Nat.add_comm] at htm hbase
  simp [highTarget,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    initial,originalValues,intermediate,seedSlots,backSlots,frontSlots,widthSlots,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  omega

theorem cost_append (as bs : List ActivePrefixStageHeadersOps.Op) (st : ActiveRepairRankHeadersCommands.State) :
    ActivePrefixStageHeadersOps.scheduleCost (as++bs) st=
      ActivePrefixStageHeadersOps.scheduleCost as st+
      ActivePrefixStageHeadersOps.scheduleCost bs (ActivePrefixStageHeadersOps.execute as st) := by
  induction as generalizing st with
  | nil => simp [ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.execute]
  | cons op ops ih => simp only [List.cons_append,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.execute,ih]; omega

def lowPrefix : List ActivePrefixStageHeadersOps.Op := [
  .command (.difference 6 12 24 (by decide)),.command (.difference 24 22 25 (by decide)),
  .command (.erase 24),.product ![7,25,24] (by decide),.command (.erase 25)]
def lowRest : List ActivePrefixStageHeadersOps.Op := [
  .command (.add 24 9 (by decide)),.product ![0,24,25] (by decide),.command (.erase 24),
  .command (.add 25 10 (by decide)),.command (.copy 25 17 (by decide)),.command (.erase 25)]
def sourcePrefix : Order → List ActivePrefixStageHeadersOps.Op
  | .early => [.command (.difference 12 11 24 (by decide)),.command (.difference 24 22 25 (by decide)),
      .command (.erase 24),.product ![7,25,24] (by decide),.command (.erase 25)]
  | .late => [.command (.difference 6 11 24 (by decide)),.command (.difference 24 22 25 (by decide)),
      .command (.erase 24),.product ![7,25,24] (by decide),.command (.erase 25)]
def sourceRest : Order → List ActivePrefixStageHeadersOps.Op
  | .early => [.product ![0,24,25] (by decide),.command (.erase 24),
      .command (.difference 0 10 24 (by decide)),.command (.add 25 24 (by decide)),
      .command (.copy 25 21 (by decide)),.command (.erase 24),.command (.erase 25)]
  | .late => [.command (.add 24 9 (by decide)),.product ![0,24,25] (by decide),.command (.erase 24),
      .command (.copy 25 21 (by decide)),.command (.erase 25)]
def sourceAxes (order : Order) (v : Stage s) := match order with
  | .early => (v.target.val-v.source.val-1)*v.f
  | .late => (v.slots-v.source.val-1)*v.f

theorem low_prefix_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) :
    ActivePrefixStageHeadersOps.execute lowPrefix (intermediate order v rows highSlots)=
      ActiveRepairRankHeadersCommands.put (intermediate order v rows highSlots) 24 ((v.slots-v.target.val-1)*v.f) := by
  funext i; fin_cases i
  all_goals simp [lowPrefix,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,originalValues,
    intermediate,seedSlots,backSlots,frontSlots,widthSlots,highSlots,finished,outputs,Function.update,Nat.mul_comm]

theorem source_prefix_eq {s : Shape} (order : Order) (v : Stage s) (rows : ℕ) :
    ActivePrefixStageHeadersOps.execute (sourcePrefix order) (intermediate order v rows lowSlots)=
      ActiveRepairRankHeadersCommands.put (intermediate order v rows lowSlots) 24 (sourceAxes order v) := by
  cases order <;> funext i <;> fin_cases i
  all_goals simp [sourcePrefix,sourceAxes,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,originalValues,
    intermediate,seedSlots,backSlots,frontSlots,widthSlots,highSlots,lowSlots,finished,outputs,Function.update,Nat.mul_comm]

theorem lowTarget_cost_bound {s : Shape} (order : Order) (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs order v i≤A) :
    ActivePrefixStageHeadersOps.scheduleCost (lowTarget) (intermediate order v rows highSlots)≤50000*(A+1) := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  have ho0 : s.chunk≤A := ho (0 : Fin 13)
  have ho1 : s.axes≤A := ho (1 : Fin 13)
  have ho2 : s.guard≤A := ho (2 : Fin 13)
  have ho3 : s.active≤A := ho (3 : Fin 13)
  have ho4 : rows≤A := ho (4 : Fin 13)
  have ho5 : s.payload≤A := ho (5 : Fin 13)
  have ho6 : v.slots≤A := ho (6 : Fin 13)
  have ho7 : v.f≤A := ho (7 : Fin 13)
  have ho8 : v.left≤A := ho (8 : Fin 13)
  have ho9 : v.right≤A := ho (9 : Fin 13)
  have ho10 : v.rho≤A := ho (10 : Fin 13)
  have ho11 : v.source.val≤A := ho (11 : Fin 13)
  have ho12 : v.target.val≤A := ho (12 : Fin 13)
  have hv0 : s.axes*s.guard≤A := hv (0 : Fin 9)
  have hv1 : s.B≤A := hv (1 : Fin 9)
  have hv2 : s.F≤A := hv (2 : Fin 9)
  have hv3 : before v≤A := hv (3 : Fin 9)
  have hv4 : after v≤A := hv (4 : Fin 9)
  have hv5 : (v.f-1)*s.chunk≤A := hv (5 : Fin 9)
  have hv6 : (v.f-1)*s.guard≤A := hv (6 : Fin 9)
  have hv7 : v.f-1≤A := hv (7 : Fin 9)
  have hv8 : offset order v≤A := hv (8 : Fin 9)
  simp only [Nat.mul_comm] at hv0 hv5 hv6
  have htm : (v.slots-v.target.val-1)*v.f≤((v.slots-v.target.val-1)*v.f+v.right)*s.chunk :=
    (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _ hK)
  have hbase : ((v.slots-v.target.val-1)*v.f+v.right)*s.chunk≤after v := by unfold after lowAxes; omega
  simp only [Nat.mul_comm,Nat.add_comm] at htm hbase
  change ActivePrefixStageHeadersOps.scheduleCost (lowPrefix++lowRest) (intermediate order v rows highSlots)≤50000*(A+1)
  rw [cost_append,low_prefix_eq]
  simp [lowPrefix,lowRest,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    initial,originalValues,intermediate,seedSlots,backSlots,frontSlots,widthSlots,highSlots,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  omega

theorem source_early_cost_bound {s : Shape} (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs .early v i≤A) :
    ActivePrefixStageHeadersOps.scheduleCost (source .early) (intermediate .early v rows lowSlots)≤50000*(A+1) := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  have ho0 : s.chunk≤A := ho (0 : Fin 13)
  have ho1 : s.axes≤A := ho (1 : Fin 13)
  have ho2 : s.guard≤A := ho (2 : Fin 13)
  have ho3 : s.active≤A := ho (3 : Fin 13)
  have ho4 : rows≤A := ho (4 : Fin 13)
  have ho5 : s.payload≤A := ho (5 : Fin 13)
  have ho6 : v.slots≤A := ho (6 : Fin 13)
  have ho7 : v.f≤A := ho (7 : Fin 13)
  have ho8 : v.left≤A := ho (8 : Fin 13)
  have ho9 : v.right≤A := ho (9 : Fin 13)
  have ho10 : v.rho≤A := ho (10 : Fin 13)
  have ho11 : v.source.val≤A := ho (11 : Fin 13)
  have ho12 : v.target.val≤A := ho (12 : Fin 13)
  have hv0 : s.axes*s.guard≤A := hv (0 : Fin 9)
  have hv1 : s.B≤A := hv (1 : Fin 9)
  have hv2 : s.F≤A := hv (2 : Fin 9)
  have hv3 : before v≤A := hv (3 : Fin 9)
  have hv4 : after v≤A := hv (4 : Fin 9)
  have hv5 : (v.f-1)*s.chunk≤A := hv (5 : Fin 9)
  have hv6 : (v.f-1)*s.guard≤A := hv (6 : Fin 9)
  have hv7 : v.f-1≤A := hv (7 : Fin 9)
  have hv8 : offset .early v≤A := hv (8 : Fin 9)
  simp only [Nat.mul_comm] at hv0 hv5 hv6
  dsimp only [offset] at hv8
  have htm : (v.target.val-v.source.val-1)*v.f≤(v.target.val-v.source.val-1)*v.f*s.chunk :=
    Nat.le_mul_of_pos_right _ hK
  have hbase : (v.target.val-v.source.val-1)*v.f*s.chunk≤earlyOffset v := by unfold earlyOffset; omega
  simp only [Nat.mul_comm] at htm hbase
  change ActivePrefixStageHeadersOps.scheduleCost (sourcePrefix .early++sourceRest .early) (intermediate .early v rows lowSlots)≤50000*(A+1)
  rw [cost_append,source_prefix_eq]
  simp [sourcePrefix,sourceRest,sourceAxes,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    initial,originalValues,intermediate,seedSlots,backSlots,frontSlots,widthSlots,highSlots,lowSlots,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  omega

theorem source_late_cost_bound {s : Shape} (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs .late v i≤A) :
    ActivePrefixStageHeadersOps.scheduleCost (source .late) (intermediate .late v rows lowSlots)≤50000*(A+1) := by
  have hH : 0<s.H := positive_H v hG
  have hK : 0<s.chunk := by have := v.selectedFits; omega
  have hb := CompactGadgetReservationHeadersData.roundBack_eq s hH hK
  have hf := CompactGadgetReservationHeadersData.roundFront_eq s hH hK
  change RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B at hb
  change RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F at hf
  have ho0 : s.chunk≤A := ho (0 : Fin 13)
  have ho1 : s.axes≤A := ho (1 : Fin 13)
  have ho2 : s.guard≤A := ho (2 : Fin 13)
  have ho3 : s.active≤A := ho (3 : Fin 13)
  have ho4 : rows≤A := ho (4 : Fin 13)
  have ho5 : s.payload≤A := ho (5 : Fin 13)
  have ho6 : v.slots≤A := ho (6 : Fin 13)
  have ho7 : v.f≤A := ho (7 : Fin 13)
  have ho8 : v.left≤A := ho (8 : Fin 13)
  have ho9 : v.right≤A := ho (9 : Fin 13)
  have ho10 : v.rho≤A := ho (10 : Fin 13)
  have ho11 : v.source.val≤A := ho (11 : Fin 13)
  have ho12 : v.target.val≤A := ho (12 : Fin 13)
  have hv0 : s.axes*s.guard≤A := hv (0 : Fin 9)
  have hv1 : s.B≤A := hv (1 : Fin 9)
  have hv2 : s.F≤A := hv (2 : Fin 9)
  have hv3 : before v≤A := hv (3 : Fin 9)
  have hv4 : after v≤A := hv (4 : Fin 9)
  have hv5 : (v.f-1)*s.chunk≤A := hv (5 : Fin 9)
  have hv6 : (v.f-1)*s.guard≤A := hv (6 : Fin 9)
  have hv7 : v.f-1≤A := hv (7 : Fin 9)
  have hv8 : offset .late v≤A := hv (8 : Fin 9)
  simp only [Nat.mul_comm] at hv0 hv5 hv6
  dsimp only [offset] at hv8
  have htm : (v.slots-v.source.val-1)*v.f≤((v.slots-v.source.val-1)*v.f+v.right)*s.chunk :=
    (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _ hK)
  have hbase : ((v.slots-v.source.val-1)*v.f+v.right)*s.chunk=lateOffset v := rfl
  simp only [Nat.mul_comm,Nat.add_comm] at htm hbase
  change ActivePrefixStageHeadersOps.scheduleCost (sourcePrefix .late++sourceRest .late) (intermediate .late v rows lowSlots)≤50000*(A+1)
  rw [cost_append,source_prefix_eq]
  simp [sourcePrefix,sourceRest,sourceAxes,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    initial,originalValues,intermediate,seedSlots,backSlots,frontSlots,widthSlots,highSlots,lowSlots,
    Function.update,Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm,Nat.add_comm,two_mul] at hb hf ⊢
  omega

theorem source_cost_bound {s : Shape} (order : Order) (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs order v i≤A) :
    ActivePrefixStageHeadersOps.scheduleCost (source order) (intermediate order v rows lowSlots)≤50000*(A+1) := by
  cases order
  · exact source_early_cost_bound v rows A hG ho hv
  · exact source_late_cost_bound v rows A hG ho hv

theorem execute_append (as bs : List ActivePrefixStageHeadersOps.Op) (st : ActiveRepairRankHeadersCommands.State) :
    ActivePrefixStageHeadersOps.execute (as++bs) st=
      ActivePrefixStageHeadersOps.execute bs (ActivePrefixStageHeadersOps.execute as st) := by
  induction as generalizing st with
  | nil => rfl
  | cons op ops ih => exact ih _

theorem arithmetic_bound {s : Shape} (order : Order) (v : Stage s) (rows A : ℕ)
    (hG : 1≤s.guard) (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs order v i≤A) :
    ActivePrefixStageHeadersRun.cost order v rows≤400000*(A+1) := by
  have h0 := seed_cost_bound order v rows A hG ho hv
  have h1 := back_cost_bound order v rows A hG ho hv
  have h2 := front_cost_bound order v rows A hG ho hv
  have h3 := widths_cost_bound order v rows A hG ho hv
  have h4 := highTarget_cost_bound order v rows A hG ho hv
  have h5 := lowTarget_cost_bound order v rows A hG ho hv
  have h6 := source_cost_bound order v rows A hG ho hv
  unfold ActivePrefixStageHeadersRun.cost schedule
  simp only [cost_append,execute_append,seed_eq order v rows,back_eq order v rows hG,front_eq order v rows hG,
    width_eq order v rows hG,high_eq order v rows hG,low_eq order v rows hG,source_eq order v rows hG]
  have he : ActivePrefixStageHeadersOps.scheduleCost [.command (.erase 22)]
      (intermediate order v rows sourceSlots)=201 := by
    simp [ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,intermediate,
      ActiveRepairRankHeadersCommands.cost]
  rw [he]
  omega

 theorem original_bounds {s : Shape} (order : Order) (v : Stage s) (rows : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (horder : Ordered order v)
    (hrows : 0<rows) (hrecord : s.bits+1≤s.payload) :
    (∀ i, originalValues v rows i≤rows*s.recordWidth) ∧
      (∀ i, outputs order v i≤rows*s.recordWidth) := by
  let p := parameters v hG hGK
  let mode : ActivePrefixLayoutHeadersData.Mode := match order with | .early => .target | .late => .compactAfter
  have hfit : offset order v+p.f*p.q≤ActivePrefixLayoutHeadersGeometry.room s p mode := by
    cases order
    · exact early_fits v horder
    · exact late_fits v horder
  have hl := ActivePrefixLayoutHeadersGeometry.originals_bound s p (offset order v) rows mode hfit hrows hrecord
  have hd := positive_axes v
  have hf := v.positiveWidth
  have hs := v.source.isLt
  have ht := v.target.isLt
  have ha := v.activeAxes
  have hwidth := v.widthFits
  have hH : s.H≤rows*s.recordWidth := hl 0
  have hK : s.chunk≤rows*s.recordWidth := hl 7
  have hb : s.guard≤rows*s.recordWidth := hl 8
  have hr : v.rho≤rows*s.recordWidth := hl 10
  have hrow : rows≤rows*s.recordWidth := hl 12
  have hpay : s.payload≤rows*s.recordWidth := hl 13
  have hbits : s.bits≤rows*s.recordWidth := by omega
  have hactive : s.active≤s.bits := by
    have hkp : 0<s.chunk := by have := v.selectedFits; omega
    have hab : s.active*s.chunk≤s.bits := by unfold Shape.bits; omega
    nlinarith
  have haxes : s.axes≤rows*s.recordWidth := by change s.axes*s.guard≤_ at hH; nlinarith
  have hslots : v.slots≤s.active := by nlinarith
  constructor
  · intro i; fin_cases i <;> simp [originalValues]
    all_goals omega
  · intro i; fin_cases i
    · exact hl 0
    · exact hl 1
    · exact hl 2
    · exact hl 3
    · exact hl 4
    · exact hl 5
    · exact hl 6
    · exact hl 9
    · exact hl 11

def RoutingBounded (st : ActivePrefixStageHeadersRouting.State) (A : ℕ) := ∀ i, (st i).getD 0≤A

theorem routing_eval_bounded (c : ActivePrefixStageHeadersRouting.Command)
    (st : ActivePrefixStageHeadersRouting.State) (A : ℕ) (hb : RoutingBounded st A) :
    RoutingBounded (ActivePrefixStageHeadersRouting.eval c st) A := by
  intro i
  cases c with
  | copy src dst h =>
    by_cases hi : i=dst
    · simpa [ActivePrefixStageHeadersRouting.eval,ActivePrefixStageHeadersRouting.put,Function.update,hi] using hb src
    · simpa [ActivePrefixStageHeadersRouting.eval,ActivePrefixStageHeadersRouting.put,Function.update,hi] using hb i
  | erase dst =>
    by_cases hi : i=dst
    · simp [ActivePrefixStageHeadersRouting.eval,Function.update,hi]
    · simpa [ActivePrefixStageHeadersRouting.eval,Function.update,hi] using hb i

theorem routing_cost_bound (cs : List ActivePrefixStageHeadersRouting.Command)
    (st : ActivePrefixStageHeadersRouting.State) (A : ℕ) (hb : RoutingBounded st A) :
    ActivePrefixStageHeadersRouting.scheduleCost cs st≤cs.length*(100*(A+1)+1) := by
  induction cs generalizing st with
  | nil => simp [ActivePrefixStageHeadersRouting.scheduleCost]
  | cons c cs ih =>
    have h0 : ActivePrefixStageHeadersRouting.cost c st≤100*(A+1) := by
      cases c with
      | copy src dst h => simp only [ActivePrefixStageHeadersRouting.cost]; have hh := hb src; omega
      | erase dst => simp only [ActivePrefixStageHeadersRouting.cost]; have hh := hb dst; omega
    have h1 := ih (ActivePrefixStageHeadersRouting.eval c st) (routing_eval_bounded c st A hb)
    simp only [ActivePrefixStageHeadersRouting.scheduleCost,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem lift_finished_bounded {s : Shape} (order : Order) (v : Stage s) (rows A : ℕ)
    (ho : ∀ i, originalValues v rows i≤A) (hv : ∀ i, outputs order v i≤A) :
    RoutingBounded (ActivePrefixStageHeadersPlaced.lift (finished order v rows)) A := by
  intro i
  by_cases h28 : i.val<28
  · simp only [ActivePrefixStageHeadersPlaced.lift,h28,↓reduceDIte]
    by_cases h13 : i.val<13
    · simpa only [finished,h13,↓reduceDIte,Option.getD_some] using ho ⟨i.val,h13⟩
    · by_cases h22 : i.val<22
      · simpa only [finished,h13,h22,↓reduceDIte,Option.getD_some] using hv ⟨i.val-13,by omega⟩
      · simp [finished,h13,h22]
  · simp [ActivePrefixStageHeadersPlaced.lift,h28]

theorem uniform_bound {s : Shape} (order : Order) (v : Stage s) (rows : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (horder : Ordered order v)
    (hrows : 0<rows) (hrecord : s.bits+1≤s.payload) :
    ActivePrefixStageHeadersPlaced.cost order v rows≤1000000*(rows*s.recordWidth) := by
  obtain ⟨ho,hv⟩ := original_bounds order v rows hG hGK horder hrows hrecord
  have ha := arithmetic_bound order v rows (rows*s.recordWidth) hG ho hv
  have hr := routing_cost_bound ActivePrefixStageHeadersPlaced.schedule
    (ActivePrefixStageHeadersPlaced.lift (finished order v rows)) (rows*s.recordWidth)
    (lift_finished_bounded order v rows (rows*s.recordWidth) ho hv)
  have hlen : ActivePrefixStageHeadersPlaced.schedule.length=31 := rfl
  rw [hlen] at hr
  have hp : 0<s.payload := by omega
  have hvolume : 1≤rows*s.recordWidth := by
    have hpv : 0<s.recordWidth := by unfold Shape.recordWidth; positivity
    have hm := Nat.mul_pos hrows hpv
    omega
  unfold ActivePrefixStageHeadersPlaced.cost
  omega

end IntegerMultBounds.Machine.ActivePrefixStageHeadersBudget
