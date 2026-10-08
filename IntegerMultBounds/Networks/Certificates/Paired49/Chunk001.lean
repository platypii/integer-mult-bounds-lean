import IntegerMultBounds.Networks.Certificates.Paired49.Data

/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.
Regenerate with scripts/generate_paired49_certificate.py. -/

namespace IntegerMultBounds.Networks.Certificates.Paired49
open MaskDAG
set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

theorem chunk001_checked : checkChunk bank.lookup 128 chunk001 = true := by
  decide +kernel

theorem chunk001_length : chunk001.length = 128 := by rfl

theorem chunk001_additions : chunk001.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 0 := by decide +kernel

end IntegerMultBounds.Networks.Certificates.Paired49
