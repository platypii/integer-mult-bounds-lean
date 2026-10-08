import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk291

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk295_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 13899157573376917406468665818267) chunk295 = true := by
  decide +kernel

theorem chunk295_last : lastKey (some 13899157573376917406468665818267) chunk295 = some 14449194985091733545112251153406 := by
  decide +kernel

theorem chunk295_length : chunk295.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
