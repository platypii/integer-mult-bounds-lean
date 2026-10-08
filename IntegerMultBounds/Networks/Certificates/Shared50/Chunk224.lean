import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk220

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk224_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2878720599731616643585159921251) chunk224 = true := by
  decide +kernel

theorem chunk224_last : lastKey (some 2878720599731616643585159921251) chunk224 = some 2900318196254945801029190742570 := by
  decide +kernel

theorem chunk224_length : chunk224.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
