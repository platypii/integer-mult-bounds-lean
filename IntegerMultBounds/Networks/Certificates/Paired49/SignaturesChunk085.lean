import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk081

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures085_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 10880
    chunk085 signatures085 = true := by
  decide +kernel

theorem signatures085_length : signatures085.length = 109 := by rfl

theorem signatures085_empty_core_additions : (chunk085.zip signatures085).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 69 := by
  decide +kernel

theorem signatures085_nonempty_core_additions : (chunk085.zip signatures085).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 40 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
