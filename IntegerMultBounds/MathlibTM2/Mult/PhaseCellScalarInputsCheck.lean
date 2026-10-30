module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallInverseParameters
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank

/-! Audit allocation, ordinary input loading and disposal without numerical imports. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.zeroWordBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.initializeScalarBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.installScalarInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.installInverseParameters_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.inverseParameterState_inputs,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.inverseParameterState_zero,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releaseScalarBank_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Ordinary scalar input allocation/load/release axiom audit passed."
