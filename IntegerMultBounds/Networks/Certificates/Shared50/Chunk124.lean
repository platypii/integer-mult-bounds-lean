import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk120

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk124_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 497143682283887175232308859247) chunk124 = true := by
  decide +kernel

theorem chunk124_last : lastKey (some 497143682283887175232308859247) chunk124 = some 511208411710576168818310471020 := by
  decide +kernel

theorem chunk124_length : chunk124.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
