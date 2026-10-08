import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk076

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures080_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 10240
    chunk080 signatures080 = true := by
  decide +kernel

theorem signatures080_length : signatures080.length = 128 := by rfl

theorem signatures080_empty_core_additions : (chunk080.zip signatures080).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 78 := by
  decide +kernel

theorem signatures080_nonempty_core_additions : (chunk080.zip signatures080).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 50 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
