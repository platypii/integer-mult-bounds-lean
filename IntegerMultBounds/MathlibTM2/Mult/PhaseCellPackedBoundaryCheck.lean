module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPublicationProgram
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledPackedBoundaryPublish
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloLookup

/-! Integrity audit for the executed packed boundary movement components.
This audits these components only; S4 acceptance requires their solver and
full-tensor integration. -/

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedAdvanceBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.releasedBoundaryAdvanceControls_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedPublicationProgram_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryScatter_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedBoundaryPublish_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.controlledPackedBoundaryPublish_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.loadPackedLookupBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedLookupCounters_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.maskedPackedAmbientWord_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.binaryPackedHaloLookup_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed boundary movement axiom audit passed."
