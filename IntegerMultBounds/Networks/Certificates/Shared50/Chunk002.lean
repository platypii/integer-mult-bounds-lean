import IntegerMultBounds.Networks.Certificates.Shared50.Data

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk002_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4564718210909734999905424) chunk002 = true := by
  decide +kernel

theorem chunk002_last : lastKey (some 4564718210909734999905424) chunk002 = some 4780525609031772350951282 := by
  decide +kernel

theorem chunk002_length : chunk002.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
