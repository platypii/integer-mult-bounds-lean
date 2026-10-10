import IntegerMultBounds.Machine.AllAxisAddressHeaders

/-! Physical complete-address initialization costs linear reserved payload,
including full width-header derivation, counter filling and header erasure. -/
namespace IntegerMultBounds.Machine.AllAxisAddressInitBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
variable {s : Shape}

theorem derive_bound (order : Order) (v : Stage s) (rows : ℕ) :
    CompactChildHeadersArithmetic.scheduleCost AllAxisAddressHeaders.schedule
      (AllAxisAddressHeaders.initial order v rows)≤1000*(s.bits+1) := by
  simp [AllAxisAddressHeaders.schedule,CompactChildHeadersArithmetic.scheduleCost,
    CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    AllAxisAddressHeaders.initial,AllAxisPhaseHeadersData.initial,
    ActivePrefixStageHeadersData.finished,ActivePrefixStageHeadersData.originalValues,
    ActivePrefixStageHeadersData.outputs,ActiveRepairRankHeadersCommands.put,Function.update]
  unfold Shape.bits
  nlinarith

end IntegerMultBounds.Machine.AllAxisAddressInitBudget
