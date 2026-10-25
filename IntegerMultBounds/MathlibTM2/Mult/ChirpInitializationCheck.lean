module

import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputMultiplierSetup
import IntegerMultBounds.MathlibTM2.Mult.ChirpBankClear
import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardParameterSetup
import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardOutputBank
import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardConsumerSetup
import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardBankPlacement
import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardSourceLoad
import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardRawSetup
import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardCallerSize
import Lean.Util.CollectAxioms

/-! Integrity audit of executed bank loading, multiplier preparation and bank release. -/

open Lean in
run_cmd do
  for name in #[`IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardRawSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardTableWord_quadratic,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardCaller_fits,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardSourceLoad_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.ForwardBankPlacement.source_injective,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.ForwardBankPlacement.consumers_injective,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.ForwardBankPlacement.consumers_source,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.ForwardBankPlacement.consumers_pairwise,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankEmissionSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankEmissionSetup_holds,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpForwardCallerParameters_do,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankFamily_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardConsumerSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardCoefficient_values,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankClone_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpForwardOutputBank_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpForwardRing_do,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpForwardPrecision_do,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpForwardParameters_do,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.tblChirpMultiplierDimensions_do,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpMultiplierSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpMultiplierSetup_ready,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputMultiplierSetup_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpOutputMultiplierSetup_base,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankCopies_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankLoad_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankLoad_holds,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankLoad_off,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankClear_exec,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankClear_empty,
      `IntegerMultBounds.MathlibTM2.Mult.ShortConv.chirpBankClear_load] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Chirp initialization and bank release axiom audit passed."
