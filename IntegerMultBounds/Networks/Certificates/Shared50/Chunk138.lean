import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk134

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk138_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 641644491315664112351299139054) chunk138 = true := by
  decide +kernel

theorem chunk138_last : lastKey (some 641644491315664112351299139054) chunk138 = some 677213735210266283360902510576 := by
  decide +kernel

theorem chunk138_length : chunk138.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
