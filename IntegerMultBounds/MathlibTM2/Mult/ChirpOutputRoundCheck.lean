module

import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFinish
import Lean.Util.CollectAxioms

/-! Integrity audit of the executed final chirp precision reduction. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputRound_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputRound_exec

open Lean in
run_cmd do
  for name in #[`IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputFinish_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpCrop_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpCrop_stream_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpRound_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpRounded_norm,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpRounded_fits,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputRound_exec] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp output precision reduction axiom audit passed."
