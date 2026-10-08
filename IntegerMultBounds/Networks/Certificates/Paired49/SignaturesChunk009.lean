import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk005

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures009_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 1152
    chunk009 signatures009 = true := by
  decide +kernel

theorem signatures009_length : signatures009.length = 128 := by rfl

theorem signatures009_empty_core_additions : (chunk009.zip signatures009).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 34 := by
  decide +kernel

theorem signatures009_nonempty_core_additions : (chunk009.zip signatures009).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 70 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
