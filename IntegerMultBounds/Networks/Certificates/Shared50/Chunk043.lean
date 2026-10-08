import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk039

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk043_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 39834278161898176501813022) chunk043 = true := by
  decide +kernel

theorem chunk043_last : lastKey (some 39834278161898176501813022) chunk043 = some 41471278854596569155274288 := by
  decide +kernel

theorem chunk043_length : chunk043.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
