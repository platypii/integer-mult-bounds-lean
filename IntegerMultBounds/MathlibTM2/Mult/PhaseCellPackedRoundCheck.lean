module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizePackedBatch

/-! Audit local rounding without importing the ambient numerical caller. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishRoundedBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.normalizePackedBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generateDoubleWidth_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.publishRoundedKey_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.widenPackedKey_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedFinalRoundInterval_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedFinalRoundBatch_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.transformPrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.widenPackedPrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedIntervalRead_finalRound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedFinalRound_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedFinalRoundBatch_accuracy,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.roundPackedKey_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.roundPackedBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.roundPackedPrefix_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed local rounding axiom audit passed."
