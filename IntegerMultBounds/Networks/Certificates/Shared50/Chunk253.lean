import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk249

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk253_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4774479702692347711893799857957) chunk253 = true := by
  decide +kernel

theorem chunk253_last : lastKey (some 4774479702692347711893799857957) chunk253 = some 4858926329371610518094394819154 := by
  decide +kernel

theorem chunk253_length : chunk253.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
