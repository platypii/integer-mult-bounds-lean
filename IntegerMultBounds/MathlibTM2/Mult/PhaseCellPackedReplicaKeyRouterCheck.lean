module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyRoutingCost

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyPlanesInterchange_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedReplicaKeyRouter_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.countedPackedReplicaKeyRouter_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedReplicaKeyRoutingCost_uniform ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed replica/key router axiom audit passed."
