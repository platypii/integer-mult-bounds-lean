module

import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherExec
import IntegerMultBounds.MathlibTM2.Mult.ChirpWindows
import Lean.Util.CollectAxioms

/-! Integrity audit of overlapping-window geometry and the executable sweep step. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpWindow_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpWindow_getD

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpAdvance_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpAdvance_sum

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.gatherPacket_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.gatherPacket_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.gatherBatch_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.gatherBatch_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGather_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpGather_exec

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp gather axiom audit passed."
