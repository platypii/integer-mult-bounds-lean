import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk305

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk309_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 83902879113757938137303015920727) chunk309 = true := by
  decide +kernel

theorem chunk309_last : lastKey (some 83902879113757938137303015920727) chunk309 = some 99760403575748000812976087817652 := by
  decide +kernel

theorem chunk309_length : chunk309.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
