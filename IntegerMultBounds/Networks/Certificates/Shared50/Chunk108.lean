import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk104

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk108_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 367499268007223610827580595606) chunk108 = true := by
  decide +kernel

theorem chunk108_last : lastKey (some 367499268007223610827580595606) chunk108 = some 371068032904791808750580325631 := by
  decide +kernel

theorem chunk108_length : chunk108.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
