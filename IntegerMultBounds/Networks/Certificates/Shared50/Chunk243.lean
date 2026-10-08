import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk239

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk243_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3941045128383503817479082889007) chunk243 = true := by
  decide +kernel

theorem chunk243_last : lastKey (some 3941045128383503817479082889007) chunk243 = some 4012457597187324661708491457631 := by
  decide +kernel

theorem chunk243_length : chunk243.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
