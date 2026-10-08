import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk112

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk116_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 437962436012572874259953932908) chunk116 = true := by
  decide +kernel

theorem chunk116_last : lastKey (some 437962436012572874259953932908) chunk116 = some 440039446988401962517228812033 := by
  decide +kernel

theorem chunk116_length : chunk116.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
