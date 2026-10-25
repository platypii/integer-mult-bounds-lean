module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReferenceSpec
import Lean.Util.CollectAxioms

/-! Integrity audit of the shared inverse endpoint and its reference implementation. -/

open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface.ErrorOn.trans,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface.ErrorOn.crop,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface.norm_error_of_publish,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface.SolveSpec.with_locality,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface.SolveSpec.of_windows,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface.SolveSpec.full_error,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface.pcSolve_spec] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Shared phase-cell interface axiom audit passed."
