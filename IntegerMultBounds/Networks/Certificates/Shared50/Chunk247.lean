import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk243

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk247_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4299344738219439546044693944471) chunk247 = true := by
  decide +kernel

theorem chunk247_last : lastKey (some 4299344738219439546044693944471) chunk247 = some 4335153722759583645522803668279 := by
  decide +kernel

theorem chunk247_length : chunk247.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
