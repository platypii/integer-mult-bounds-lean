import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk111

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk115_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 416337623941539029835447927234) chunk115 = true := by
  decide +kernel

theorem chunk115_last : lastKey (some 416337623941539029835447927234) chunk115 = some 437962436012572874259953932908 := by
  decide +kernel

theorem chunk115_length : chunk115.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
