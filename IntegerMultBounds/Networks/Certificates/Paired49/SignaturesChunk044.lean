import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk040

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures044_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 5632
    chunk044 signatures044 = true := by
  decide +kernel

theorem signatures044_length : signatures044.length = 128 := by rfl

theorem signatures044_empty_core_additions : (chunk044.zip signatures044).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures044_nonempty_core_additions : (chunk044.zip signatures044).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
