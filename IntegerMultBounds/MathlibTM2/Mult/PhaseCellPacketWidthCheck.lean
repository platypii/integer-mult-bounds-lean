module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketWidth

/-! Keep the packet-format audit independent of the large numerical closure. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.narrowPackets_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.widenPackets_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.narrowPackets_cost_le ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packet width conversion axiom audit passed."
