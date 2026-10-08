import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk057

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures061_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 7808
    chunk061 signatures061 = true := by
  decide +kernel

theorem signatures061_length : signatures061.length = 128 := by rfl

theorem signatures061_empty_core_additions : (chunk061.zip signatures061).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures061_nonempty_core_additions : (chunk061.zip signatures061).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
