import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk246

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk250_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4636585922598072724560715667479) chunk250 = true := by
  decide +kernel

theorem chunk250_last : lastKey (some 4636585922598072724560715667479) chunk250 = some 4680333793614426969284078479537 := by
  decide +kernel

theorem chunk250_length : chunk250.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
