module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCount
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCountRemoval
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedReplicaPadding
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRemoveDummyReplicas
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedReplicaTile

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaCount_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaCountRemoval_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.retainedReplicaPadding_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.removeDummyPrefix_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.removeDummyPrefix_cost_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.removeDummyReplicas_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ownedPrefixPadding_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedTilePrefixPadding_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedTilePrefixPaddingCost_le,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.tilePrefixPad_drop,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.tilePrefixPad_pair_view,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedReplicaTilePadding_exec ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Replica tile padding axiom audit passed."
