import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk290

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk294_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 13298925018982914247103659262323) chunk294 = true := by
  decide +kernel

theorem chunk294_last : lastKey (some 13298925018982914247103659262323) chunk294 = some 13899157573376917406468665818267 := by
  decide +kernel

theorem chunk294_length : chunk294.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
