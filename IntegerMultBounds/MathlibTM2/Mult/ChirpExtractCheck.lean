module

import IntegerMultBounds.MathlibTM2.Mult.ChirpExtract
import Lean.Util.CollectAxioms

/-! Standalone integrity audit of chirp coefficient reversal and extraction. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.reverseWords_coeffs_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.reverseWords_coeffs_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationCoeffs_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationCoeffs_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationTape_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationTape_err

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp extraction axiom audit passed."
