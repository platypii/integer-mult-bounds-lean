import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk062

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures066_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 8448
    chunk066 signatures066 = true := by
  decide +kernel

theorem signatures066_length : signatures066.length = 128 := by rfl

theorem signatures066_empty_core_additions : (chunk066.zip signatures066).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 77 := by
  decide +kernel

theorem signatures066_nonempty_core_additions : (chunk066.zip signatures066).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 51 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
