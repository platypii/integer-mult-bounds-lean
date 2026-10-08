import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk194

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk198_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1802048723687278535423965475387) chunk198 = true := by
  decide +kernel

theorem chunk198_last : lastKey (some 1802048723687278535423965475387) chunk198 = some 1826005005088627759861536306248 := by
  decide +kernel

theorem chunk198_length : chunk198.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
