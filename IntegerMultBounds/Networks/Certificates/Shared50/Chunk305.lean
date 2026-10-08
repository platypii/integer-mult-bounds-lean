import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk301

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk305_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 40079227035157884806780530774823) chunk305 = true := by
  decide +kernel

theorem chunk305_last : lastKey (some 40079227035157884806780530774823) chunk305 = some 48491877167161642536942604188763 := by
  decide +kernel

theorem chunk305_length : chunk305.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
