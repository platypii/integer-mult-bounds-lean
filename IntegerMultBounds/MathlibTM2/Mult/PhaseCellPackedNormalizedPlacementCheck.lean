module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedPlacement

/-! Audit the concrete packed normalization bank and its descriptor handoff. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.descriptorSolverCall_exec_bank,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.descriptorSolverCall_exec_on,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.descriptorSolverCall_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedScalarReg_injective,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedScalarReg_bounds,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedPort_injective,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedScalarReg_port,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedScalarReg_header,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedRegisters_nodup,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedDescriptorCall_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyNormalizedBatch_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed normalized placement axiom audit passed."
