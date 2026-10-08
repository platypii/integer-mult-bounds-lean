import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk016

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures020_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 2560
    chunk020 signatures020 = true := by
  decide +kernel

theorem signatures020_length : signatures020.length = 128 := by rfl

theorem signatures020_empty_core_additions : (chunk020.zip signatures020).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 128 := by
  decide +kernel

theorem signatures020_nonempty_core_additions : (chunk020.zip signatures020).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
