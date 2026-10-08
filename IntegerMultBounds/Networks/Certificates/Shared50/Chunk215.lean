import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk211

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk215_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2400808539241320812252417237593) chunk215 = true := by
  decide +kernel

theorem chunk215_last : lastKey (some 2400808539241320812252417237593) chunk215 = some 2447116258992066724980078242088 := by
  decide +kernel

theorem chunk215_length : chunk215.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
