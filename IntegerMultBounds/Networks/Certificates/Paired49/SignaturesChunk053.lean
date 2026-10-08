import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk049

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures053_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 6784
    chunk053 signatures053 = true := by
  decide +kernel

theorem signatures053_length : signatures053.length = 128 := by rfl

theorem signatures053_empty_core_additions : (chunk053.zip signatures053).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures053_nonempty_core_additions : (chunk053.zip signatures053).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
