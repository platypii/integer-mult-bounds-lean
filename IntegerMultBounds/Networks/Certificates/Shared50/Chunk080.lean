import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk076

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk080_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 202226191977313291932239274919) chunk080 = true := by
  decide +kernel

theorem chunk080_last : lastKey (some 202226191977313291932239274919) chunk080 = some 206839958814961192904277024103 := by
  decide +kernel

theorem chunk080_length : chunk080.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
