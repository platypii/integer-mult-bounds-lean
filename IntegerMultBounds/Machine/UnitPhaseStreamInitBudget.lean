import IntegerMultBounds.Machine.UnitPhaseStreamInit

/-! Physical complete-address initialization costs linear reserved payload,
including full width-header derivation, counter filling and header erasure. -/
namespace IntegerMultBounds.Machine.UnitPhaseStreamInitBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
variable {s : Shape}

theorem derive_bound (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    CompactChildHeadersArithmetic.scheduleCost UnitPhaseAddressHeaders.schedule
      (UnitPhaseAddressHeaders.initial order v rows axis)≤1000*(s.bits+1) := by
  simp [UnitPhaseAddressHeaders.schedule,CompactChildHeadersArithmetic.scheduleCost,
    CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    UnitPhaseAddressHeaders.initial,SparsePhaseHeadersData.initial,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,ActiveRepairRankHeadersCommands.put,Function.update]
  unfold Shape.bits
  nlinarith

theorem cost_payload (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (hrecord : s.bits+1≤s.payload) : UnitPhaseStreamInit.cost order v rows axis≤1100*s.payload := by
  have hd := derive_bound order v rows axis
  have hl := ActiveRepairRankHeadersCommands.bits_length s.bits
  unfold UnitPhaseStreamInit.cost
  omega

end IntegerMultBounds.Machine.UnitPhaseStreamInitBudget
