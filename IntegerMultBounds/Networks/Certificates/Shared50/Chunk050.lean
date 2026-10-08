import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk046

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk050_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 59921076844485584238325841) chunk050 = true := by
  decide +kernel

theorem chunk050_last : lastKey (some 59921076844485584238325841) chunk050 = some 63458206685447522523935426 := by
  decide +kernel

theorem chunk050_length : chunk050.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
