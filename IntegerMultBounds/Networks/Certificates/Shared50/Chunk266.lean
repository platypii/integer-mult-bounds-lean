import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk262

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk266_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 6299205607974196006316525930150) chunk266 = true := by
  decide +kernel

theorem chunk266_last : lastKey (some 6299205607974196006316525930150) chunk266 = some 6363569277015983820557796384434 := by
  decide +kernel

theorem chunk266_length : chunk266.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
