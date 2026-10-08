import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk207

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk211_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2249052400771347876620037757529) chunk211 = true := by
  decide +kernel

theorem chunk211_last : lastKey (some 2249052400771347876620037757529) chunk211 = some 2352265951131177679819997262424 := by
  decide +kernel

theorem chunk211_length : chunk211.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
