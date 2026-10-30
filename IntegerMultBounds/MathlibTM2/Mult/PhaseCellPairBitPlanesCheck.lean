module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairBitPlaneData
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinBitPlanes

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.copyMappedWords_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.copyPairBitPlanes_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.joinBitPlanes_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.cstream_pairBits_roundtrip,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyPair_real,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyPair_imag ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed pair bit-plane codec axiom audit passed."
