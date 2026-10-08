import IntegerMultBounds.Networks.Certificates.Paired49.Data
import IntegerMultBounds.Networks.Certificates.Paired49.Chunk001

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk005_checked : checkChunk bank.lookup 640 chunk005 = true := by
  decide +kernel

theorem chunk005_length : chunk005.length = 128 := by rfl

theorem chunk005_additions : chunk005.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 0 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
