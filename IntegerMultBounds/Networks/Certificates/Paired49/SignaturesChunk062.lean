import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk058

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures062_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 7936
    chunk062 signatures062 = true := by
  decide +kernel

theorem signatures062_length : signatures062.length = 128 := by rfl

theorem signatures062_empty_core_additions : (chunk062.zip signatures062).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 0 := by
  decide +kernel

theorem signatures062_nonempty_core_additions : (chunk062.zip signatures062).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 128 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
