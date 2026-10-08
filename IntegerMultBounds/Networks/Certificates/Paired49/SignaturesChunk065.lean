import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk061

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures065_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 8320
    chunk065 signatures065 = true := by
  decide +kernel

theorem signatures065_length : signatures065.length = 128 := by rfl

theorem signatures065_empty_core_additions : (chunk065.zip signatures065).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 78 := by
  decide +kernel

theorem signatures065_nonempty_core_additions : (chunk065.zip signatures065).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 50 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
