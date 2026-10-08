import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk008

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures012_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 1536
    chunk012 signatures012 = true := by
  decide +kernel

theorem signatures012_length : signatures012.length = 128 := by rfl

theorem signatures012_empty_core_additions : (chunk012.zip signatures012).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 42 := by
  decide +kernel

theorem signatures012_nonempty_core_additions : (chunk012.zip signatures012).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 86 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
