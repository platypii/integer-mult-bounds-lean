import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk252

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk256_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5173849530526568340664727376521) chunk256 = true := by
  decide +kernel

theorem chunk256_last : lastKey (some 5173849530526568340664727376521) chunk256 = some 5215957188464800402621206546281 := by
  decide +kernel

theorem chunk256_length : chunk256.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
