import IntegerMultBounds.Networks.Certificates.Paired49.Data
import IntegerMultBounds.Networks.Certificates.Paired49.Chunk008

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk012_checked : checkChunk bank.lookup 1536 chunk012 = true := by
  decide +kernel

theorem chunk012_length : chunk012.length = 128 := by rfl

theorem chunk012_additions : chunk012.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 128 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
