import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures000_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 0
    chunk000 signatures000 = true := by
  decide +kernel

theorem signatures000_length : signatures000.length = 128 := by rfl

theorem signatures000_empty_core_additions : (chunk000.zip signatures000).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures000_nonempty_core_additions : (chunk000.zip signatures000).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
