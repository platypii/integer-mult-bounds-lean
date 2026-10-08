import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk000

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures004_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 512
    chunk004 signatures004 = true := by
  decide +kernel

theorem signatures004_length : signatures004.length = 128 := by rfl

theorem signatures004_empty_core_additions : (chunk004.zip signatures004).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures004_nonempty_core_additions : (chunk004.zip signatures004).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 0 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
