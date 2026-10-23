module

import IntegerMultBounds.MathlibTM2.Mult.ChirpGeneratedBatchCorrect
import IntegerMultBounds.MathlibTM2.Mult.ChirpInputBatch
import Lean.Util.CollectAxioms

/-! Integrity audit of generated-operand shared execution and actual tape correctness. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGeneratedBatch_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGeneratedBatch_correct

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpInputBatch_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpInputBatch_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp generated shared batch axiom audit passed."
