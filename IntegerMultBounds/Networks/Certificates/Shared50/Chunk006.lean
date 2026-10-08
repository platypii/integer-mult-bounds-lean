import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk002

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk006_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5342388478392164877459076) chunk006 = true := by
  decide +kernel

theorem chunk006_last : lastKey (some 5342388478392164877459076) chunk006 = some 5482735970608881403317890 := by
  decide +kernel

theorem chunk006_length : chunk006.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
