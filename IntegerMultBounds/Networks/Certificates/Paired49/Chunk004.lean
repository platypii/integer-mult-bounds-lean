import IntegerMultBounds.Networks.Certificates.Paired49.Data
import IntegerMultBounds.Networks.Certificates.Paired49.Chunk000

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk004_checked : checkChunk bank.lookup 512 chunk004 = true := by
  decide +kernel

theorem chunk004_length : chunk004.length = 128 := by rfl

theorem chunk004_additions : chunk004.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 0 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
