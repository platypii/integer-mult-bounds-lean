import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk072

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk076_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 184339624207834422338352667225) chunk076 = true := by
  decide +kernel

theorem chunk076_last : lastKey (some 184339624207834422338352667225) chunk076 = some 185314282513563840285619533924 := by
  decide +kernel

theorem chunk076_length : chunk076.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
