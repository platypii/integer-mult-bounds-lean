import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk013

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures017_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 2176
    chunk017 signatures017 = true := by
  decide +kernel

theorem signatures017_length : signatures017.length = 128 := by rfl

theorem signatures017_empty_core_additions : (chunk017.zip signatures017).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 118 := by
  decide +kernel

theorem signatures017_nonempty_core_additions : (chunk017.zip signatures017).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 10 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
