module

import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherSetup
import Lean.Util.CollectAxioms

/-! Integrity audit of generated gathering controls and their composition with the sweep. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpControlBatch_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpControlBatch_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGatherSetup_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGatherSetup_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp control-generation axiom audit passed."
