import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk204

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk208_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2152609573788885185000132631026) chunk208 = true := by
  decide +kernel

theorem chunk208_last : lastKey (some 2152609573788885185000132631026) chunk208 = some 2166563936898567987632043696125 := by
  decide +kernel

theorem chunk208_length : chunk208.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
