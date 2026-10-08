import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk068

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures072_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 9216
    chunk072 signatures072 = true := by
  decide +kernel

theorem signatures072_length : signatures072.length = 128 := by rfl

theorem signatures072_empty_core_additions : (chunk072.zip signatures072).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 78 := by
  decide +kernel

theorem signatures072_nonempty_core_additions : (chunk072.zip signatures072).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 50 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
