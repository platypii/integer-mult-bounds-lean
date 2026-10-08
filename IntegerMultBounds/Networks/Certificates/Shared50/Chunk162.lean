import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk158

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk162_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 979680613343432345316196316117) chunk162 = true := by
  decide +kernel

theorem chunk162_last : lastKey (some 979680613343432345316196316117) chunk162 = some 1034056096947752203196977101497 := by
  decide +kernel

theorem chunk162_length : chunk162.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
