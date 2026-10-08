import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk003

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures007_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 896
    chunk007 signatures007 = true := by
  decide +kernel

theorem signatures007_length : signatures007.length = 128 := by rfl

theorem signatures007_empty_core_additions : (chunk007.zip signatures007).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures007_nonempty_core_additions : (chunk007.zip signatures007).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
