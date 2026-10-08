import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk030

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures034_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 4352
    chunk034 signatures034 = true := by
  decide +kernel

theorem signatures034_length : signatures034.length = 128 := by rfl

theorem signatures034_empty_core_additions : (chunk034.zip signatures034).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 109 := by
  decide +kernel

theorem signatures034_nonempty_core_additions : (chunk034.zip signatures034).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 19 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
