import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk191

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk195_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1745676639524612521450863689819) chunk195 = true := by
  decide +kernel

theorem chunk195_last : lastKey (some 1745676639524612521450863689819) chunk195 = some 1757291782172236097908409188224 := by
  decide +kernel

theorem chunk195_length : chunk195.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
