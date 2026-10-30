module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComplexBatchAssembly

/-! Audit local complex output assembly independently of the numerical solver. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBatchHalves_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedComplexBatchAssembly_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedComplexBatchFinish_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairComplexPrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairComplexKey_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseComplexCounts_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairPackedBatches_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairPackedBatchHalves_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBatch_pair,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedIntervalRead_pair_components,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairedPackedComponents_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.pairedComponentFields_accuracy ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed complex output axiom audit passed."
