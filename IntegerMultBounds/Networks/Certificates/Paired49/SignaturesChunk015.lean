import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk011

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures015_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 1920
    chunk015 signatures015 = true := by
  decide +kernel

theorem signatures015_length : signatures015.length = 128 := by rfl

theorem signatures015_empty_core_additions : (chunk015.zip signatures015).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 53 := by
  decide +kernel

theorem signatures015_nonempty_core_additions : (chunk015.zip signatures015).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 75 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
