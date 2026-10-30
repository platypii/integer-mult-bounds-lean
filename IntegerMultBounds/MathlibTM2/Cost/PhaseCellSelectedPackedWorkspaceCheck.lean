module

import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedWorkspace
import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedPublication
import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedInteriorCost
import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedPreparedCost

/-! Audit selected resource comparisons for the actual packed caller. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Cost.packedBoundaryDataCost_poly,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloInputTapeCost_poly,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloPreparedInputCost_le_stages,
      `IntegerMultBounds.MathlibTM2.Cost.preparedResidualSolveCost_poly,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloPreparedInputCost_weights_poly,
      `IntegerMultBounds.MathlibTM2.Cost.retainedPageSpatialGuardedStepCost_poly,
      `IntegerMultBounds.MathlibTM2.Cost.retainedPageSpatialIntervalLoopCost_poly,
      `IntegerMultBounds.MathlibTM2.Cost.preparedSharedLocalFeedCouplingIntervalCost_poly,
      `IntegerMultBounds.MathlibTM2.Cost.packedBoundaryRecoveryInputsCost_poly,
      `IntegerMultBounds.MathlibTM2.Cost.packedBoundaryRecoveryCost_geometry_le,
      `IntegerMultBounds.MathlibTM2.Cost.packedBoundaryRecoveryCost_weights_poly,
      `IntegerMultBounds.MathlibTM2.Cost.sharedCouplingCoefficientIntervalCost_poly,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloInteriorCoefficientsCost_geometry_le,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloInteriorCoefficientsCost_weights_poly,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloKeyCost_le_bound,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloKeyLoopCost_le_bound,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloKeyLoopCost_geometry_le,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloKeyLoopCost_interior_le,
      `IntegerMultBounds.MathlibTM2.Cost.packedHaloKeyLoopCost_weights_poly,
      `IntegerMultBounds.MathlibTM2.Cost.reusablePackedCellBatchPublishCost_le_bound,
      `IntegerMultBounds.MathlibTM2.Cost.selectedPackedPublication_poly_le,
      `IntegerMultBounds.MathlibTM2.Cost.selectedPackedPublication_scaled_volume_le,
      `IntegerMultBounds.MathlibTM2.Cost.selectedPackedWorkspaceReplica_poly_le,
      `IntegerMultBounds.MathlibTM2.Cost.selectedPackedNormalizedWorkspace_le_shared_add_linear,
      `IntegerMultBounds.MathlibTM2.Cost.selectedPackedWorkspaceReplica_scaled_volume_le ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Selected packed workspace axiom audit passed."
