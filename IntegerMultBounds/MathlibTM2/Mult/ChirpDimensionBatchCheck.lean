module

import IntegerMultBounds.MathlibTM2.Mult.ChirpDimensionBatch
import IntegerMultBounds.MathlibTM2.Mult.ChirpInputBatch
import Lean.Util.CollectAxioms

/-! Integrity audit of shared execution with generated and erased caller dimensions. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpDimensionBatch_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpDimensionBatch_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp installed dimension batch axiom audit passed."
