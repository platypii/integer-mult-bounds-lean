import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk075

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures079_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 10112
    chunk079 signatures079 = true := by
  decide +kernel

theorem signatures079_length : signatures079.length = 128 := by rfl

theorem signatures079_empty_core_additions : (chunk079.zip signatures079).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 77 := by
  decide +kernel

theorem signatures079_nonempty_core_additions : (chunk079.zip signatures079).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 51 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
