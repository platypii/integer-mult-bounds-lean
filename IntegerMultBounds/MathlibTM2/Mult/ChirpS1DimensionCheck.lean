module

import IntegerMultBounds.MathlibTM2.Mult.ChirpS1DimensionFrame
import IntegerMultBounds.MathlibTM2.Mult.ChirpInputBatch
import Lean.Util.CollectAxioms

/-! Integrity audit of shared-caller dimension arithmetic, emission and bank restoration. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpS1DimensionSetup_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpS1DimensionSetup_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp S1 dimension setup axiom audit passed."
