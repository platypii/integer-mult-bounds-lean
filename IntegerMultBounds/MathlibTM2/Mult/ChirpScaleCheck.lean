module

import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputEExec
import Lean.Util.CollectAxioms

/-! Integrity audit of executed output shifts and signed output bounds. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpScale_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpScale_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputETable_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputETable_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp output shift axiom audit passed."
