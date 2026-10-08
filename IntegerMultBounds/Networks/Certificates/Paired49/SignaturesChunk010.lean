import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk006

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures010_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 1280
    chunk010 signatures010 = true := by
  decide +kernel

theorem signatures010_length : signatures010.length = 128 := by rfl

theorem signatures010_empty_core_additions : (chunk010.zip signatures010).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 42 := by
  decide +kernel

theorem signatures010_nonempty_core_additions : (chunk010.zip signatures010).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 86 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
