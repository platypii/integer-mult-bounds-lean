module

import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchProductMath
import Lean.Util.CollectAxioms

/-! Standalone integrity audit of the complete shared correlation-batch product. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBatchProduct_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBatchProduct_exec

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationBatchTape_chirpRingCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationBatchTape_chirpRingCorr

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationBatchTape_chirpCorr_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.correlationBatchTape_chirpCorr_err

open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds.MathlibTM2.Mult.ShortConv).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Shared chirp batch product axiom audit passed."
