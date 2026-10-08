import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk036

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures040_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 5120
    chunk040 signatures040 = true := by
  decide +kernel

theorem signatures040_length : signatures040.length = 128 := by rfl

theorem signatures040_empty_core_additions : (chunk040.zip signatures040).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures040_nonempty_core_additions : (chunk040.zip signatures040).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
