import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk227

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk231_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3206120219427664792327671696129) chunk231 = true := by
  decide +kernel

theorem chunk231_last : lastKey (some 3206120219427664792327671696129) chunk231 = some 3229858138841449149985355489565 := by
  decide +kernel

theorem chunk231_length : chunk231.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
