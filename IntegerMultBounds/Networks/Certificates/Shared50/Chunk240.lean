import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk236

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk240_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3838324419122530419261496982147) chunk240 = true := by
  decide +kernel

theorem chunk240_last : lastKey (some 3838324419122530419261496982147) chunk240 = some 3870752473239448467585518286431 := by
  decide +kernel

theorem chunk240_length : chunk240.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
