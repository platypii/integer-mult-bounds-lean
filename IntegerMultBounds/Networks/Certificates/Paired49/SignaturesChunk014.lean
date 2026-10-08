import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk010

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures014_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 1792
    chunk014 signatures014 = true := by
  decide +kernel

theorem signatures014_length : signatures014.length = 128 := by rfl

theorem signatures014_empty_core_additions : (chunk014.zip signatures014).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 42 := by
  decide +kernel

theorem signatures014_nonempty_core_additions : (chunk014.zip signatures014).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 86 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
