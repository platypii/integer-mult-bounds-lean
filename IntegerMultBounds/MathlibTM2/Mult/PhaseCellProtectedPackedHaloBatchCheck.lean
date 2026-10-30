module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyBatchCost
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyNormalizedBatch

/-! Audit the actual protected numerical supplier independently of routing. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalizePackedBatchCost_affine,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalizePackedReplicaCost_le_volume,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.preparedNormalizePackedBatchCost_affine,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyNormalizedBatchCost_affine,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyNormalizedReplicaCost_le_local_volume,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloPreparedInputCost_le_normalizedReplicaCost,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBatchStepCost_le_normalizedReplicaCost,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyNormalizedBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyComplexBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyComplexExpand_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyComplexRealBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedKeyBankViews.external_update,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBatchCostFromSetup_zero,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyRealBatchCost_affine,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyRealBatchCost_two_components,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyRealBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedKeyBankViews.input_update,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedKeyBankViews.factory_view,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBatch_from_setup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.protectedPackedHaloGeometryPublishedBatch_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Protected packed numerical batch axiom audit passed."
