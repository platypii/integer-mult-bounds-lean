module

import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedWorkspace
import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedPublication
import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedKeyCost

/-! Audit selected resource comparisons for the actual packed caller. -/
open Lean in
run_cmd do
  for name in #[
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
