import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk253

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk257_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5215957188464800402621206546281) chunk257 = true := by
  decide +kernel

theorem chunk257_last : lastKey (some 5215957188464800402621206546281) chunk257 = some 5264441218955221937839765268673 := by
  decide +kernel

theorem chunk257_length : chunk257.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
