module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryPowerChain

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.unaryPowerChain_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.unaryPowerChain_release_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.unaryPowerChainR_get,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.unaryPowerChainCost_eq,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.unaryPowerChainCost_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.unaryPowerChainVolume_le ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chunk dimension generation and release axiom audit passed."
