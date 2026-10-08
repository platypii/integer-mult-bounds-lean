import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk091

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk095_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 281793048907544987823383280629) chunk095 = true := by
  decide +kernel

theorem chunk095_last : lastKey (some 281793048907544987823383280629) chunk095 = some 291808557353470277563370778605 := by
  decide +kernel

theorem chunk095_length : chunk095.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
