import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk002

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures006_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 768
    chunk006 signatures006 = true := by
  decide +kernel

theorem signatures006_length : signatures006.length = 128 := by rfl

theorem signatures006_empty_core_additions : (chunk006.zip signatures006).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures006_nonempty_core_additions : (chunk006.zip signatures006).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
