import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk001

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures005_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 640
    chunk005 signatures005 = true := by
  decide +kernel

theorem signatures005_length : signatures005.length = 128 := by rfl

theorem signatures005_empty_core_additions : (chunk005.zip signatures005).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures005_nonempty_core_additions : (chunk005.zip signatures005).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
