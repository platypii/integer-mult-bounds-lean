import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk241

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk245_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4233525118464124431077401763599) chunk245 = true := by
  decide +kernel

theorem chunk245_last : lastKey (some 4233525118464124431077401763599) chunk245 = some 4263796711907369468738152249630 := by
  decide +kernel

theorem chunk245_length : chunk245.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
