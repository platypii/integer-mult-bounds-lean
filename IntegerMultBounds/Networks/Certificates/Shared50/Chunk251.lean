import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk247

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk251_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4680333793614426969284078479537) chunk251 = true := by
  decide +kernel

theorem chunk251_last : lastKey (some 4680333793614426969284078479537) chunk251 = some 4724435512497054348709902213409 := by
  decide +kernel

theorem chunk251_length : chunk251.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
