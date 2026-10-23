module

import IntegerMultBounds.MathlibTM2.Mult.ChirpMakeX
import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandCountSetup
import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandProduct
import Lean.Util.CollectAxioms

/-! Integrity audit of composed input arithmetic, cleanup and generated counters. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpMakeX_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpMakeX_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOperandCountSetup_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOperandCountSetup_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp input production axiom audit passed."
