import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk078

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures082_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 10496
    chunk082 signatures082 = true := by
  decide +kernel

theorem signatures082_length : signatures082.length = 128 := by rfl

theorem signatures082_empty_core_additions : (chunk082.zip signatures082).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 79 := by
  decide +kernel

theorem signatures082_nonempty_core_additions : (chunk082.zip signatures082).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 49 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
