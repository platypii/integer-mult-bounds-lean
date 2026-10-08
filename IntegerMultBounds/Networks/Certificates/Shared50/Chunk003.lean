import IntegerMultBounds.Networks.Certificates.Shared50.Data

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk003_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4780525609031772350951282) chunk003 = true := by
  decide +kernel

theorem chunk003_last : lastKey (some 4780525609031772350951282) chunk003 = some 4972654219697812664490385 := by
  decide +kernel

theorem chunk003_length : chunk003.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
