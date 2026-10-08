import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk098

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk102_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 327478252689425365188283428631) chunk102 = true := by
  decide +kernel

theorem chunk102_last : lastKey (some 327478252689425365188283428631) chunk102 = some 329627403215543010677200823303 := by
  decide +kernel

theorem chunk102_length : chunk102.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
