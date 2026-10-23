module

import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherFromDimensions
import Lean.Util.CollectAxioms

/-! Integrity audit of raw-line gathering with all geometry setup generated and erased. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpRawGather_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpRawGather_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBlockCountSetup_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBlockCountSetup_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGatherFromDimensions_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGatherFromDimensions_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp raw-line gathering axiom audit passed."
