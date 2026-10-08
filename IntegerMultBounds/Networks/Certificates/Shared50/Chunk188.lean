import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk184

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk188_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1568751331810115776340300430456) chunk188 = true := by
  decide +kernel

theorem chunk188_last : lastKey (some 1568751331810115776340300430456) chunk188 = some 1579327369147056433133524409124 := by
  decide +kernel

theorem chunk188_length : chunk188.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
