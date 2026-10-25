module

import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardSelected
import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardTableSize
import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardWindowSetup
import Lean.Util.CollectAxioms

/-! Integrity audit of the returned-tape semantics and explicit forward parameter choices. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardSelected_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardSelected_error

open Lean in
run_cmd do
  for name in #[`IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGeneratedCorrelationRows_norm,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputNumerators_getElem,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputTape_word,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardOutput_length,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardNumerators_norm,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardTape_value,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardError_gates,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardPrecision_budget,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardDecoded_error,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardSelected_error,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardWindow_sq,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardWindow_le,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardGrowth_good,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardWindow_machineGate,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardWidths_le,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardTableWord_good,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpForwardWindow_do] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp forward tape, parameter and window execution axiom audit passed."
