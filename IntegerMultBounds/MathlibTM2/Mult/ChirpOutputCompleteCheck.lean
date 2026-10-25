module

import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputComplete
import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFactorSetup
import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDimensionSetup
import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDecode
import Lean.Util.CollectAxioms

/-! Integrity audit of the composed output machine and generated factor/dimension setup. -/

/-- info: 'IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputComplete_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputComplete_exec

open Lean in
run_cmd do
  for name in #[`IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputFinished_coeff,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputFinished_value,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblComputedUnaryCopies_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputDimensionSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputDimensions_at,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputDimensions_off,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputComplete_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputNumerators_length,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputNumerators_norm,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpNormalization_do,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpNormalizationSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpOutputReducedTable_do,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputTableSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputFactorSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputFactors_bound,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpOutputDimensions_do,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpOutputDimensionsClear_do] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp complete output and generated setup axiom audit passed."
