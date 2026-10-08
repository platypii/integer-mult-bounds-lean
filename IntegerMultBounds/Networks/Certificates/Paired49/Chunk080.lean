import IntegerMultBounds.Networks.Certificates.Paired49.Data
import IntegerMultBounds.Networks.Certificates.Paired49.Chunk076

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk080_checked : checkChunk bank.lookup 10240 chunk080 = true := by
  decide +kernel

theorem chunk080_length : chunk080.length = 128 := by rfl

theorem chunk080_additions : chunk080.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 128 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
