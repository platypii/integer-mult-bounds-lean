import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk105

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk109_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 371068032904791808750580325631) chunk109 = true := by
  decide +kernel

theorem chunk109_last : lastKey (some 371068032904791808750580325631) chunk109 = some 388754430987624548289284537095 := by
  decide +kernel

theorem chunk109_length : chunk109.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
