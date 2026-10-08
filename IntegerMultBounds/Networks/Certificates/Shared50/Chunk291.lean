import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk287

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk291_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 11977449778321725369686391016972) chunk291 = true := by
  decide +kernel

theorem chunk291_last : lastKey (some 11977449778321725369686391016972) chunk291 = some 12318935537935748735714244409679 := by
  decide +kernel

theorem chunk291_length : chunk291.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
