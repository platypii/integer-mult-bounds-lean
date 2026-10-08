import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk070

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures074_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 9472
    chunk074 signatures074 = true := by
  decide +kernel

theorem signatures074_length : signatures074.length = 128 := by rfl

theorem signatures074_empty_core_additions : (chunk074.zip signatures074).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 78 := by
  decide +kernel

theorem signatures074_nonempty_core_additions : (chunk074.zip signatures074).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 50 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
