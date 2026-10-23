module

import IntegerMultBounds.MathlibTM2.Mult.ChirpComputedApprox
import IntegerMultBounds.MathlibTM2.Mult.ChirpTableCorrelation
import Lean.Util.CollectAxioms

/-! Integrity audit of output arithmetic and the computed-factor approximation bridge. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputWord_chirpAR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputWord_chirpAR

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpComputed_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpComputed_approx

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp output arithmetic axiom audit passed."
