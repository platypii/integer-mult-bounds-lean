module

import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedDescriptorWords

/-! Audit the ordinary packed descriptor construction and its exact bank views. -/
open Lean in
run_cmd do
  for name in #[
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyDescriptorInput_view,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyPublicationInput_view,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyPublicationInput_radius,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyPublicationInput_fresh,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyDescriptorInput_left,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyDescriptorInput_views,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyDescriptorInput_native,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyDescriptorInput_headers,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedKeyDescriptorInput_fresh,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedInputBank_view,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedInputBank_width,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedInputBank_scalar,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedInputBank_parameters,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.packedNormalizedInputBank_ports,
      `IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.descriptorReadyBank_packedNormalized ] do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo "Packed normalized descriptor words axiom audit passed."
