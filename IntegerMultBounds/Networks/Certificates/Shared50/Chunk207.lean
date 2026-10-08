import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk203

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk207_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2135974716802502707434242159261) chunk207 = true := by
  decide +kernel

theorem chunk207_last : lastKey (some 2135974716802502707434242159261) chunk207 = some 2152609573788885185000132631026 := by
  decide +kernel

theorem chunk207_length : chunk207.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
