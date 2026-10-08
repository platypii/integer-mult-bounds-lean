import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk193

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk197_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1768975074209175625549024551959) chunk197 = true := by
  decide +kernel

theorem chunk197_last : lastKey (some 1768975074209175625549024551959) chunk197 = some 1802048723687278535423965475387 := by
  decide +kernel

theorem chunk197_length : chunk197.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
