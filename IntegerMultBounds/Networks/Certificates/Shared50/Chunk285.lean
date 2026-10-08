import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk281

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk285_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 9979330724809788381549603811641) chunk285 = true := by
  decide +kernel

theorem chunk285_last : lastKey (some 9979330724809788381549603811641) chunk285 = some 10161806254870523464700250733002 := by
  decide +kernel

theorem chunk285_length : chunk285.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
