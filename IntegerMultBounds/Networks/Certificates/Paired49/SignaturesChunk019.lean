import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk015

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures019_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 2432
    chunk019 signatures019 = true := by
  decide +kernel

theorem signatures019_length : signatures019.length = 128 := by rfl

theorem signatures019_empty_core_additions : (chunk019.zip signatures019).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 128 := by
  decide +kernel

theorem signatures019_nonempty_core_additions : (chunk019.zip signatures019).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
