import IntegerMultBounds.Machine.AllAxisPhaseHeadersData

/-! Descriptor setup for the single all-axis address scan is linear in the
full address width, with no coefficient-volume or axis-pass multiplier. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseHeadersBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open AllAxisPhaseHeadersData
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (put)
variable {s : Shape}

theorem cost_bound (order : Order) (v : Stage s) (rows m : ℕ)
    (hm : 0<m) (hslots : m≤v.slots) :
    scheduleCost (schedule m) (initial order v rows)≤10000*(s.bits+1) := by
  have hf := v.positiveWidth
  have hq : 0<s.chunk := by have := v.selectedFits; omega
  have hfit := fits v m hslots
  have hmf : 0<m*v.f := Nat.mul_pos hm hf
  have hact : 0<s.active := by omega
  have hfAct : v.f≤s.active := by nlinarith
  have hmAct : m≤m*v.f := Nat.le_mul_of_pos_right _ hf
  have hcAct : s.chunk≤s.active*s.chunk := Nat.le_mul_of_pos_left _ hact
  have hactive : s.active≤s.active*s.chunk := Nat.le_mul_of_pos_right _ hq
  have hlow : s.active-(v.left+m*v.f)+1≤s.active := by omega
  have hlowProd := Nat.mul_le_mul_right s.chunk hlow
  have hbits : s.H+s.B+s.active*s.chunk≤s.bits := by unfold Shape.bits; omega
  have hlen := ActiveRepairRankHeadersCommands.bits_length m
  have hone := ActiveRepairRankHeadersCommands.bits_length 1
  have hrho := v.selectedFits
  simp [schedule,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,put,initial,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,RecursiveChildQuotientsConstant.cost,Function.update,Nat.mul_comm]
  nlinarith

end IntegerMultBounds.Machine.AllAxisPhaseHeadersBudget
