import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk250

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk254_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4858926329371610518094394819154) chunk254 = true := by
  decide +kernel

theorem chunk254_last : lastKey (some 4858926329371610518094394819154) chunk254 = some 5126099326790228406670125504057 := by
  decide +kernel

theorem chunk254_length : chunk254.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
