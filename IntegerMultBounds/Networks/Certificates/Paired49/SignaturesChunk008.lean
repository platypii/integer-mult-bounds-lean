import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk004

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures008_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 1024
    chunk008 signatures008 = true := by
  decide +kernel

theorem signatures008_length : signatures008.length = 128 := by rfl

theorem signatures008_empty_core_additions : (chunk008.zip signatures008).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures008_nonempty_core_additions : (chunk008.zip signatures008).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
