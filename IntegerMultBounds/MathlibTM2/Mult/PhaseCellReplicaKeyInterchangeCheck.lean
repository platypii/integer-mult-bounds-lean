module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyInterchange

/-! Keep the bulk-routing audit separate from the numerical coupling closure. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyWords_getElem?,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.keyReplicaWords_blocks,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyWords_swap,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyInterchange_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyBitInterchange_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Replica/key interchange axiom audit passed."
