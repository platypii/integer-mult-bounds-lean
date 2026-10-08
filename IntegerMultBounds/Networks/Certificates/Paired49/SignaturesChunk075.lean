import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk071

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures075_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 9600
    chunk075 signatures075 = true := by
  decide +kernel

theorem signatures075_length : signatures075.length = 128 := by rfl

theorem signatures075_empty_core_additions : (chunk075.zip signatures075).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 77 := by
  decide +kernel

theorem signatures075_nonempty_core_additions : (chunk075.zip signatures075).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 51 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
