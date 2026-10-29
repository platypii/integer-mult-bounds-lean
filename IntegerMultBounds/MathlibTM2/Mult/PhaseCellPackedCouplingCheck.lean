module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPackedPreparedRow

/-! Audit the packed coupling execution chain. This is a component audit;
production solver integration and the full S4 endpoint remain separate gates. -/

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedCouplingOffsetLoop_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatePackedCouplingInputs_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.withSavedHeaders_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.cachedPackedCouplingRowWord_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed coupling execution axiom audit passed."
