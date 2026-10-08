import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk043

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures047_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 6016
    chunk047 signatures047 = true := by
  decide +kernel

theorem signatures047_length : signatures047.length = 128 := by rfl

theorem signatures047_empty_core_additions : (chunk047.zip signatures047).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures047_nonempty_core_additions : (chunk047.zip signatures047).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
