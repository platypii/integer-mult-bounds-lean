import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk268

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk272_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 7094667338319638720890560060262) chunk272 = true := by
  decide +kernel

theorem chunk272_last : lastKey (some 7094667338319638720890560060262) chunk272 = some 7482882642492719016521678361700 := by
  decide +kernel

theorem chunk272_length : chunk272.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
