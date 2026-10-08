import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk245

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk249_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4412762586548965006345211695999) chunk249 = true := by
  decide +kernel

theorem chunk249_last : lastKey (some 4412762586548965006345211695999) chunk249 = some 4636585922598072724560715667479 := by
  decide +kernel

theorem chunk249_length : chunk249.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
