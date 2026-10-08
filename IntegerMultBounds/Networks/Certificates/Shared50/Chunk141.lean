import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk137

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk141_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 684326665228070529413142858316) chunk141 = true := by
  decide +kernel

theorem chunk141_last : lastKey (some 684326665228070529413142858316) chunk141 = some 699789084432892802207641172181 := by
  decide +kernel

theorem chunk141_length : chunk141.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
