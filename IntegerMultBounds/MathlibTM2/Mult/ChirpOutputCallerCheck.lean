module

import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFromBanks
import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputPlacement
import Lean.Util.CollectAxioms

/-! Integrity audit of binary-bank output assembly, full cleanup and fixed register placement. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputFromBanks_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputFromBanks_exec

open Lean in
run_cmd do
  for name in #[`IntegerMultBounds.MathlibTM2.Mult.ShortConv.ChirpOutputState.install,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputRun_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputGenerated_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.ChirpOutputBase.installFactors,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.ChirpOutputLayout.clearFactors,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputFromBanks_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.OutputPlacement.layout,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.OutputPlacement.layout_cross] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp output caller, restoration and register placement axiom audit passed."
