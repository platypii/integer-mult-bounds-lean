module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyInterchange
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaChunkLayout
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkStageWiring

/-! Keep the bulk-routing audit separate from the numerical coupling closure. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyWords_getElem?,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.keyReplicaWords_blocks,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyWords_swap,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyInterchange_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKeyBitInterchange_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaKey_swap_factor,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.runReplicaChunkSwaps_words,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaChunkSwaps_volume,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.replicaChunkSwaps_positive,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.interchangeHeaders_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.generatedChunkInterchange_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.swapList_bitSymbols,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.chunkStageBits_words,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.chunkStages_shape_ready,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.chunkInterchangeLoop_exec,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.wiredChunkStages_shape,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.wiredChunkStages_bank_values ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Replica/key interchange axiom audit passed."
