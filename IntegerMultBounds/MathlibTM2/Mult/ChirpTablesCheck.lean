module

import IntegerMultBounds.MathlibTM2.Mult.ChirpTableDistance
import Lean.Util.CollectAxioms

/-! Standalone integrity audit of integer chirp table arguments and their error bounds. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpG_eq_expPi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpG_eq_expPi

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpTableE_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpTableE_err

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpTable_records_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpTable_records_norm

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpDistance_do' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpDistance_do

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp table axiom audit passed."
