import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk044

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures048_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 6144
    chunk048 signatures048 = true := by
  decide +kernel

theorem signatures048_length : signatures048.length = 128 := by rfl

theorem signatures048_empty_core_additions : (chunk048.zip signatures048).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures048_nonempty_core_additions : (chunk048.zip signatures048).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
