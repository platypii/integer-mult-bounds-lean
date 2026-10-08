import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk093

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk097_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 293265419844286010727900630365) chunk097 = true := by
  decide +kernel

theorem chunk097_last : lastKey (some 293265419844286010727900630365) chunk097 = some 295705367443311306435871580693 := by
  decide +kernel

theorem chunk097_length : chunk097.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
