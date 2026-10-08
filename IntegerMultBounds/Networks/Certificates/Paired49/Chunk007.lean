import IntegerMultBounds.Networks.Certificates.Paired49.Data
import IntegerMultBounds.Networks.Certificates.Paired49.Chunk003

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk007_checked : checkChunk bank.lookup 896 chunk007 = true := by
  decide +kernel

theorem chunk007_length : chunk007.length = 128 := by rfl

theorem chunk007_additions : chunk007.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 0 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
