import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk244

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk248_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4335153722759583645522803668279) chunk248 = true := by
  decide +kernel

theorem chunk248_last : lastKey (some 4335153722759583645522803668279) chunk248 = some 4412762586548965006345211695999 := by
  decide +kernel

theorem chunk248_length : chunk248.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
