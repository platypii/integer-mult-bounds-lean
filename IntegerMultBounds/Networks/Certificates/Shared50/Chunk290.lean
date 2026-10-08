import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk286

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk290_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 11644266210421291007128565135084) chunk290 = true := by
  decide +kernel

theorem chunk290_last : lastKey (some 11644266210421291007128565135084) chunk290 = some 11977449778321725369686391016972 := by
  decide +kernel

theorem chunk290_length : chunk290.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
