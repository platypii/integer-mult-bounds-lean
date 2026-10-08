import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk182

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk186_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1476291726809041312738260429046) chunk186 = true := by
  decide +kernel

theorem chunk186_last : lastKey (some 1476291726809041312738260429046) chunk186 = some 1492370977975312322711129142342 := by
  decide +kernel

theorem chunk186_length : chunk186.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
