module

import IntegerMultBounds.MathlibTM2.Mult.ChirpTableWordBounds
import Lean.Util.CollectAxioms

/-! Standalone integrity audit of executable chirp row-table generation and host lowering. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpNegativeStream_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpNegativeStream_host

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpOutputStream_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpOutputStream_host

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpTableWord_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpTableWord_size

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpEntryStream_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpEntryStream_decode

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp table-machine axiom audit passed."
