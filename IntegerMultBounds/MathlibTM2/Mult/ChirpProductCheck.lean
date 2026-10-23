module

import IntegerMultBounds.MathlibTM2.Mult.ChirpProductMath
import Lean.Util.CollectAxioms

/-! Standalone integrity audit of the executed single-block chirp product. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationFromUnary_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationFromUnary_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpProduct_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpProduct_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationTape_chirpRingCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationTape_chirpRingCorr

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationTape_chirpCorr_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationTape_chirpCorr_err

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp product axiom audit passed."
