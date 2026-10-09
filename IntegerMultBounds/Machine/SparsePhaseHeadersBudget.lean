import IntegerMultBounds.Machine.SparsePhaseHeadersData

/-! Sparse descriptor arithmetic is charged linearly to the actual full
address width. All runtime products are bounded geometric bit positions. -/
namespace IntegerMultBounds.Machine.SparsePhaseHeadersBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open SparsePhaseHeadersData
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (put)
open RecursiveChildQuotientsConstant (bits)
variable {s : Shape}

theorem cost_bound (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (hm : 0<m) (hslots : m≤v.slots) :
    scheduleCost (schedule m) (initial order v rows axis)≤10000*(s.bits+1) := by
  have hf := v.positiveWidth
  have hq : 0<s.chunk := by have := v.selectedFits; omega
  have hfit := last_fits v axis m hm hslots
  have hact : 1≤s.active := by omega
  have hmprod := Nat.mul_le_mul_right v.f hslots
  have hmf : (m-1)*v.f+v.f=m*v.f := by
    have h : m-1+1=m := by omega
    simpa only [Nat.add_mul,Nat.one_mul] using congrArg (fun n => n*v.f) h
  have hsplit := v.activeAxes
  have hfAct : v.f≤s.active := by omega
  have hcAct : s.chunk≤s.active*s.chunk := Nat.le_mul_of_pos_left _ hact
  have hactive : s.active≤s.active*s.chunk := Nat.le_mul_of_pos_right _ hq
  have hstride := Nat.mul_le_mul_right s.chunk hfAct
  have hlow : s.active-(v.left+(m-1)*v.f+axis.val+1)+1≤s.active := by omega
  have hlowProd := Nat.mul_le_mul_right s.chunk hlow
  have hcount : m-1≤(m-1)*v.f := Nat.le_mul_of_pos_right _ hf
  have hchunkPos := v.selectedFits
  have hbits : s.H+s.B+s.active*s.chunk≤s.bits := by unfold Shape.bits; omega
  have hlen := ActiveRepairRankHeadersCommands.bits_length (m-1)
  have hone := ActiveRepairRankHeadersCommands.bits_length 1
  simp [schedule,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,put,initial,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,RecursiveChildQuotientsConstant.cost,Function.update]
  nlinarith

theorem cost_payload (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (hm : 0<m) (hslots : m≤v.slots) (hrecord : s.bits+1≤s.payload) :
    scheduleCost (schedule m) (initial order v rows axis)≤10000*s.payload :=
  (cost_bound order v rows axis m hm hslots).trans (Nat.mul_le_mul_left _ hrecord)

end IntegerMultBounds.Machine.SparsePhaseHeadersBudget
