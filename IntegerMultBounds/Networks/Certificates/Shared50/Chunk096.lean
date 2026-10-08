import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk092

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk096_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 291808557353470277563370778605) chunk096 = true := by
  decide +kernel

theorem chunk096_last : lastKey (some 291808557353470277563370778605) chunk096 = some 293265419844286010727900630365 := by
  decide +kernel

theorem chunk096_length : chunk096.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
