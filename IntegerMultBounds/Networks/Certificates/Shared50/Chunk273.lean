import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk269

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk273_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 7482882642492719016521678361700) chunk273 = true := by
  decide +kernel

theorem chunk273_last : lastKey (some 7482882642492719016521678361700) chunk273 = some 7566058371229937825209542003400 := by
  decide +kernel

theorem chunk273_length : chunk273.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
