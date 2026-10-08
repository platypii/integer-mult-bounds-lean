import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk185

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk189_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1579327369147056433133524409124) chunk189 = true := by
  decide +kernel

theorem chunk189_last : lastKey (some 1579327369147056433133524409124) chunk189 = some 1587837649471700411576128974141 := by
  decide +kernel

theorem chunk189_length : chunk189.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
