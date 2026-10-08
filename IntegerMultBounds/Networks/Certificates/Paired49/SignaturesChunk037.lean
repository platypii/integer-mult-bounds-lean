import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk033

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures037_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 4736
    chunk037 signatures037 = true := by
  decide +kernel

theorem signatures037_length : signatures037.length = 128 := by rfl

theorem signatures037_empty_core_additions : (chunk037.zip signatures037).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures037_nonempty_core_additions : (chunk037.zip signatures037).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
