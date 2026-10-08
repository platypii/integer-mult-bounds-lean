import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk055

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures059_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 7552
    chunk059 signatures059 = true := by
  decide +kernel

theorem signatures059_length : signatures059.length = 128 := by rfl

theorem signatures059_empty_core_additions : (chunk059.zip signatures059).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures059_nonempty_core_additions : (chunk059.zip signatures059).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
