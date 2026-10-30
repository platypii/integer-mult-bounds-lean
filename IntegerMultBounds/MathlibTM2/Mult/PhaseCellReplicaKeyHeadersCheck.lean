module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyHeaders

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.binBits_size_bits,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.binBits_size_canonical,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.canonicalUnaryHeader_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.canonicalHeaderList_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyHeaders_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Replica/key canonical header axiom audit passed."
