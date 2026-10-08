import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesData
import IntegerMultBounds.Networks.Certificates.Paired49.SignaturesChunk069

/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.
Regenerate with scripts/generate_paired49_signatures.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskSignature
set_option maxRecDepth 4096

theorem signatures073_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 9344
    chunk073 signatures073 = true := by
  decide +kernel

theorem signatures073_length : signatures073.length = 128 := by rfl

theorem signatures073_empty_core_additions : (chunk073.zip signatures073).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0) = 77 := by
  decide +kernel

theorem signatures073_nonempty_core_additions : (chunk073.zip signatures073).countP (fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0) = 51 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
