import IntegerMultBounds.Networks.Certificates.Paired49.Data
import IntegerMultBounds.Networks.Certificates.Paired49.Chunk005

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk009_checked : checkChunk bank.lookup 1152 chunk009 = true := by
  decide +kernel

theorem chunk009_length : chunk009.length = 128 := by rfl

theorem chunk009_additions : chunk009.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 104 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
