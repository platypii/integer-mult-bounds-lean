import IntegerMultBounds.Networks.Certificates.Paired49.Data

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk002_checked : checkChunk bank.lookup 256 chunk002 = true := by
  decide +kernel

theorem chunk002_length : chunk002.length = 128 := by rfl

theorem chunk002_additions : chunk002.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 0 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
