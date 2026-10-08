import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk306

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk310_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 99760403575748000812976087817652) chunk310 = true := by
  decide +kernel

theorem chunk310_last : lastKey (some 99760403575748000812976087817652) chunk310 = some 118644494425609946934975441454255 := by
  decide +kernel

theorem chunk310_length : chunk310.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
