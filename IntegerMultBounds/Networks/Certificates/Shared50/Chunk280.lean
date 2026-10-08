import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk276

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk280_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 8895221758284031611723061260139) chunk280 = true := by
  decide +kernel

theorem chunk280_last : lastKey (some 8895221758284031611723061260139) chunk280 = some 9050471677590580585206882450063 := by
  decide +kernel

theorem chunk280_length : chunk280.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
