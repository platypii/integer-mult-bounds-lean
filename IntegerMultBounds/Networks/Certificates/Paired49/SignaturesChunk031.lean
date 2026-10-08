import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk027

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures031_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 3968
    chunk031 signatures031 = true := by
  decide +kernel

theorem signatures031_length : signatures031.length = 128 := by rfl

theorem signatures031_empty_core_additions : (chunk031.zip signatures031).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 128 := by
  decide +kernel

theorem signatures031_nonempty_core_additions : (chunk031.zip signatures031).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
