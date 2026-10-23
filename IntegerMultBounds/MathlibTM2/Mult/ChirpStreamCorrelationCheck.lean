module

import IntegerMultBounds.MathlibTM2.Mult.ChirpStreamCorrelation
import Lean.Util.CollectAxioms

/-! Integrity audit of operand production joined to generated-dimension shared S1 execution. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpStreamCorrelation_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpStreamCorrelation_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp stream correlation axiom audit passed."
