import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk059

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures063_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 8064
    chunk063 signatures063 = true := by
  decide +kernel

theorem signatures063_length : signatures063.length = 128 := by rfl

theorem signatures063_empty_core_additions : (chunk063.zip signatures063).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 7 := by
  decide +kernel

theorem signatures063_nonempty_core_additions : (chunk063.zip signatures063).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 121 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
