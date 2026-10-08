import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk181

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk185_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1440669688595425442772122240982) chunk185 = true := by
  decide +kernel

theorem chunk185_last : lastKey (some 1440669688595425442772122240982) chunk185 = some 1476291726809041312738260429046 := by
  decide +kernel

theorem chunk185_length : chunk185.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
