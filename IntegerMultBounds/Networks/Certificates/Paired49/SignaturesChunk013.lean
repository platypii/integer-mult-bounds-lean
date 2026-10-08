import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk009

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures013_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 1664
    chunk013 signatures013 = true := by
  decide +kernel

theorem signatures013_length : signatures013.length = 128 := by rfl

theorem signatures013_empty_core_additions : (chunk013.zip signatures013).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 41 := by
  decide +kernel

theorem signatures013_nonempty_core_additions : (chunk013.zip signatures013).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 87 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
