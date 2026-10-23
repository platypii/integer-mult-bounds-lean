module

import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicExec
import Lean.Util.CollectAxioms

/-! Integrity audit of cyclic source construction, costs and restoration. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.cyclicCopy_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.cyclicCopy_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpExtended_eq_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpExtended_eq_repeat

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpCyclic_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpCyclic_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp cyclic-source axiom audit passed."
