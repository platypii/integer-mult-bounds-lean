import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk118

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk122_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 489478595419764839139902401007) chunk122 = true := by
  decide +kernel

theorem chunk122_last : lastKey (some 489478595419764839139902401007) chunk122 = some 491768472192154680410962365327 := by
  decide +kernel

theorem chunk122_length : chunk122.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
