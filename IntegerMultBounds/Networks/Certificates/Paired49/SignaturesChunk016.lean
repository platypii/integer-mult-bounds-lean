import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk012

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures016_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 2048
    chunk016 signatures016 = true := by
  decide +kernel

theorem signatures016_length : signatures016.length = 128 := by rfl

theorem signatures016_empty_core_additions : (chunk016.zip signatures016).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 123 := by
  decide +kernel

theorem signatures016_nonempty_core_additions : (chunk016.zip signatures016).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 5 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
