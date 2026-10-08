import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk200

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk204_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2001635147232900227232374494118) chunk204 = true := by
  decide +kernel

theorem chunk204_last : lastKey (some 2001635147232900227232374494118) chunk204 = some 2019985534340312099048476768103 := by
  decide +kernel

theorem chunk204_length : chunk204.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
