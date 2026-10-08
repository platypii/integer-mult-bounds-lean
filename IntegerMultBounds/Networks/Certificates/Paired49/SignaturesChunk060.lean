import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk056

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures060_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 7680
    chunk060 signatures060 = true := by
  decide +kernel

theorem signatures060_length : signatures060.length = 128 := by rfl

theorem signatures060_empty_core_additions : (chunk060.zip signatures060).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures060_nonempty_core_additions : (chunk060.zip signatures060).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
