import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk235

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk239_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3653121779173498850609148459053) chunk239 = true := by
  decide +kernel

theorem chunk239_last : lastKey (some 3653121779173498850609148459053) chunk239 = some 3838324419122530419261496982147 := by
  decide +kernel

theorem chunk239_length : chunk239.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
