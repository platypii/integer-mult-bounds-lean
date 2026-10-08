import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk025

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures029_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 3712
    chunk029 signatures029 = true := by
  decide +kernel

theorem signatures029_length : signatures029.length = 128 := by rfl

theorem signatures029_empty_core_additions : (chunk029.zip signatures029).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 128 := by
  decide +kernel

theorem signatures029_nonempty_core_additions : (chunk029.zip signatures029).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
