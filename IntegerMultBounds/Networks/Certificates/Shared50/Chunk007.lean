import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk003

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk007_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5482735970608881403317890) chunk007 = true := by
  decide +kernel

theorem chunk007_last : lastKey (some 5482735970608881403317890) chunk007 = some 5662537049021407686050481 := by
  decide +kernel

theorem chunk007_length : chunk007.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
