import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk086

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk090_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 250125119187417850561594929534) chunk090 = true := by
  decide +kernel

theorem chunk090_last : lastKey (some 250125119187417850561594929534) chunk090 = some 260461762727604138067925427774 := by
  decide +kernel

theorem chunk090_length : chunk090.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
