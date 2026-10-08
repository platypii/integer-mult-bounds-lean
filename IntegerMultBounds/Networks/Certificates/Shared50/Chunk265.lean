import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk261

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk265_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 6235415779408491417802781953634) chunk265 = true := by
  decide +kernel

theorem chunk265_last : lastKey (some 6235415779408491417802781953634) chunk265 = some 6299205607974196006316525930150 := by
  decide +kernel

theorem chunk265_length : chunk265.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
