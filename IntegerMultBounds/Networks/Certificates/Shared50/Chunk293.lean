import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk289

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk293_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 13027566897095870945880619836531) chunk293 = true := by
  decide +kernel

theorem chunk293_last : lastKey (some 13027566897095870945880619836531) chunk293 = some 13298925018982914247103659262323 := by
  decide +kernel

theorem chunk293_length : chunk293.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
