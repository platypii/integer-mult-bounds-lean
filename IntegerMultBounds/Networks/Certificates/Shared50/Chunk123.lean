import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk119

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk123_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 491768472192154680410962365327) chunk123 = true := by
  decide +kernel

theorem chunk123_last : lastKey (some 491768472192154680410962365327) chunk123 = some 497143682283887175232308859247 := by
  decide +kernel

theorem chunk123_length : chunk123.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
