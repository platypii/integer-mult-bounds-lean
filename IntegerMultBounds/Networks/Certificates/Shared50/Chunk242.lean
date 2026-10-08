import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk238

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk242_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3903419995358166057830168369200) chunk242 = true := by
  decide +kernel

theorem chunk242_last : lastKey (some 3903419995358166057830168369200) chunk242 = some 3941045128383503817479082889007 := by
  decide +kernel

theorem chunk242_length : chunk242.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
