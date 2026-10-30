module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedKeyBatchInput
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyBatchInput
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonWidthInput
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonWidthOutput

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.keyBatchInputReg_injective,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.keyBatchSolver_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.protectedKeyBatchInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.takeKeyBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.takeCoefficientKeyBatch_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.keyBatchInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.commonWidthOutput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.commonWidthInput_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.commonWidthInput_value_fits ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Common-width numerical interface axiom audit passed."
