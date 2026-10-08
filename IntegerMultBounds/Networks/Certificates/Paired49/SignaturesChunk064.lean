import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk060

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures064_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 8192
    chunk064 signatures064 = true := by
  decide +kernel

theorem signatures064_length : signatures064.length = 128 := by rfl

theorem signatures064_empty_core_additions : (chunk064.zip signatures064).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 76 := by
  decide +kernel

theorem signatures064_nonempty_core_additions : (chunk064.zip signatures064).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 52 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
