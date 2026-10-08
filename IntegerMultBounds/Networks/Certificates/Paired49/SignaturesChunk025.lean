import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk021

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures025_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 3200
    chunk025 signatures025 = true := by
  decide +kernel

theorem signatures025_length : signatures025.length = 128 := by rfl

theorem signatures025_empty_core_additions : (chunk025.zip signatures025).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 128 := by
  decide +kernel

theorem signatures025_nonempty_core_additions : (chunk025.zip signatures025).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
