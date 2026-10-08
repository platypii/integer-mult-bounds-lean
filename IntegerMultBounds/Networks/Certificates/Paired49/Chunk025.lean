import IntegerMultBounds.Networks.Certificates.Paired49.Data
import IntegerMultBounds.Networks.Certificates.Paired49.Chunk021

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk025_checked : checkChunk bank.lookup 3200 chunk025 = true := by
  decide +kernel

theorem chunk025_length : chunk025.length = 128 := by rfl

theorem chunk025_additions : chunk025.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 128 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
