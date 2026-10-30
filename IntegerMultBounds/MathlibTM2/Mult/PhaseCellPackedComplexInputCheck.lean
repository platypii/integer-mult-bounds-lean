module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexFields

/-! Keep component-controller validation independent of the numerical solver. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.expandComplexPrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.expandComplexKey_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.expandComplexKeyCounted_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.expandComplexFields_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.complexComponentFields_norm_le ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed complex input axiom audit passed."
