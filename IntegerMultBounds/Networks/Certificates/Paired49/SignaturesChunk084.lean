import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk080

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures084_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 10752
    chunk084 signatures084 = true := by
  decide +kernel

theorem signatures084_length : signatures084.length = 128 := by rfl

theorem signatures084_empty_core_additions : (chunk084.zip signatures084).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 80 := by
  decide +kernel

theorem signatures084_nonempty_core_additions : (chunk084.zip signatures084).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 48 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
