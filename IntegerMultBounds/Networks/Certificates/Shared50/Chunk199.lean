import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk195

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk199_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1826005005088627759861536306248) chunk199 = true := by
  decide +kernel

theorem chunk199_last : lastKey (some 1826005005088627759861536306248) chunk199 = some 1922116378053433907965016224903 := by
  decide +kernel

theorem chunk199_length : chunk199.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
