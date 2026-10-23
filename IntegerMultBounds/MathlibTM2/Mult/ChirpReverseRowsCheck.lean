module

import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandReverse
import IntegerMultBounds.MathlibTM2.Mult.ChirpWeightedExec
import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandProduct
import Lean.Util.CollectAxioms

/-! Integrity audit of row reversal alongside operand production and the shared product. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOperandX_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOperandX_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp row reversal axiom audit passed."
