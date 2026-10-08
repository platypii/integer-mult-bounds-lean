import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk014

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures018_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 2304
    chunk018 signatures018 = true := by
  decide +kernel

theorem signatures018_length : signatures018.length = 128 := by rfl

theorem signatures018_empty_core_additions : (chunk018.zip signatures018).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 119 := by
  decide +kernel

theorem signatures018_nonempty_core_additions : (chunk018.zip signatures018).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 9 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
