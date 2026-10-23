module

import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchUnary
import Lean.Util.CollectAxioms

/-! Standalone integrity audit of shared batch correlation extraction. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationBatch_rpStream_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationBatch_rpStream_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationBatchFromUnary_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationBatchFromUnary_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp batch extraction axiom audit passed."
