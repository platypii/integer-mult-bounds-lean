import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk183

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk187_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1492370977975312322711129142342) chunk187 = true := by
  decide +kernel

theorem chunk187_last : lastKey (some 1492370977975312322711129142342) chunk187 = some 1568751331810115776340300430456 := by
  decide +kernel

theorem chunk187_length : chunk187.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
