module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyRoutingCost
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkTileCost
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedReplicaKeyRouter

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyPlanesInterchange_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedReplicaKeyRouter_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.countedPackedReplicaKeyRouter_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedReplicaKeyRoutingCost_uniform,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedPackedReplicaKeyRouter_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedPackedReplicaKeyRoutingCost_uniform,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.bank_volume_of_frame,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedRouterUsing_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedChunkPlanes_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedGeneratedChunkTile_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.packedGeneratedChunkTileCost_uniform ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed replica/key router axiom audit passed."
