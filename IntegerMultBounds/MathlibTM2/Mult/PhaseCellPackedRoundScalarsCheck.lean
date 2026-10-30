module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizeNativeBatch

/-! Audit scalar-only preparation and its agreement with the packed solver. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ordinaryNormalizeNativeBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ordinaryNormalizePackedBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.releaseRoundScalars_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.preparedNormalizePackedBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.prepareRoundScalars_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedRound_precision,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedRound_dimensions,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.inverseRoundVariables_injective ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed normalization scalar axiom audit passed."
