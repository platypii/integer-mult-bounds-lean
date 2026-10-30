module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyFieldsInput
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyInputCounted
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyPlacement
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPackedInput

/-! Audit the local packed entry separately from ambient inverse callers. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedInterval_map,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBatch_shift_source,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBatch_shift_bound,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedHaloSetup.packed_key_input,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedKeyFieldsInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedKeyInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedKeyInputCounted_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedKeyInput_native_view,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedKeySolver_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedScalePackets_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedInputConversion_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedInputShiftHeader_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedInputShift_value_fits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.preparedPackedInput_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Local packed numerical input axiom audit passed."
