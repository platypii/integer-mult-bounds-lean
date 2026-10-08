import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures001_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 128
    chunk001 signatures001 = true := by
  decide +kernel

theorem signatures001_length : signatures001.length = 128 := by rfl

theorem signatures001_empty_core_additions : (chunk001.zip signatures001).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures001_nonempty_core_additions : (chunk001.zip signatures001).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
