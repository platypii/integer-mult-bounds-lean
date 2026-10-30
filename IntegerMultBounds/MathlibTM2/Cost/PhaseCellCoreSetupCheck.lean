module

import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreSetupKeys

/-! Audit the generated setup partition and its production-key cost bridge. -/

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.NLogN.PhaseCellMatrix.coreSetupGroup_sum,
      `IntegerMultBounds.NLogN.PhaseCellMatrix.coreSetupGroup_subsingleton,
      `IntegerMultBounds.NLogN.PhaseCellMatrix.coreSetupGroup_eq_singleton,
      `IntegerMultBounds.NLogN.PhaseCellMatrix.coreSetupGroup_in_movement,
      `IntegerMultBounds.MathlibTM2.Cost.selectedCoreSetupKey_eq_iff,
      `IntegerMultBounds.MathlibTM2.Cost.selectedCoreSetupKeys_scaled_volume_le ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Core setup grouping axiom audit passed."
