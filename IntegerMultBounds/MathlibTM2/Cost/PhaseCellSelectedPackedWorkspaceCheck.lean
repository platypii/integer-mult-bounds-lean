module

import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedWorkspace

/-! Audit selected resource comparisons for the actual packed caller. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Cost.selectedPackedWorkspaceReplica_poly_le,
      `IntegerMultBounds.MathlibTM2.Cost.selectedPackedNormalizedWorkspace_le_shared_add_linear,
      `IntegerMultBounds.MathlibTM2.Cost.selectedPackedWorkspaceReplica_scaled_volume_le ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Selected packed workspace axiom audit passed."
