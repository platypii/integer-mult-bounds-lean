import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk064

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures068_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 8704
    chunk068 signatures068 = true := by
  decide +kernel

theorem signatures068_length : signatures068.length = 128 := by rfl

theorem signatures068_empty_core_additions : (chunk068.zip signatures068).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 77 := by
  decide +kernel

theorem signatures068_nonempty_core_additions : (chunk068.zip signatures068).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 51 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
