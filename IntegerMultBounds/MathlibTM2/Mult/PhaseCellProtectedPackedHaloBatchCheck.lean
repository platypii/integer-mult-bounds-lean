module

import IntegerMultBounds.MathlibTM2.StackLifecycleResources
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBatchTrace
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBatchStock
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloStepStock
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyBatchCost
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyNormalizedBatch

/-! Audit the actual protected numerical supplier independently of routing. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloClosedBatch_lift_within_stock,
      `IntegerMultBounds.MathlibTM2.Fast.Main.mn_release_exec_within_stock,
      `IntegerMultBounds.MathlibTM2.Fast.Main.mn_setup_exec_within_stock,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBatch_within_replica_stock,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBatch_list_exec_trace,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBatch_exec_trace,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBatch_projected_stock_le,
      `IntegerMultBounds.MathlibTM2.Host.projected_stock_le_shrinking_counter,
      `IntegerMultBounds.MathlibTM2.Host.projected_stock_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.ready_stock_le_of_queue,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.ready_stock_le_of_count,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloQueue_length,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloQueue_length_le_of_count,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.boundary,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.prefix_boundary,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.mono,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.ready,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.ready_prefix,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.split,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.prefix_archive_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.frame,
      `IntegerMultBounds.MathlibTM2.Host.embOvr_stock_le_shrinking_counter,
      `IntegerMultBounds.MathlibTM2.Host.embOvr_stock_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloQueue_length_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.ready_stock_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloBetweenInputs.right_length_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloBetweenInputs.low_length_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloProducedData.auxiliary_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.haloLowRegister_cases,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloBetweenInputs.header_length_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloBetweenInputs.native_length_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloRetainedHeaders.length_eq,
      `IntegerMultBounds.MathlibTM2.Host.hostFrameStock_congr,
      `IntegerMultBounds.MathlibTM2.Host.mnSize_mk_le_allowance,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.stock_le_cursor,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedHaloInputTrace.stock_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedHaloBatchStep_within_stock,
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
