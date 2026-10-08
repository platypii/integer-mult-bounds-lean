import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk303

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk307_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 58360896419584462185563043431216) chunk307 = true := by
  decide +kernel

theorem chunk307_last : lastKey (some 58360896419584462185563043431216) chunk307 = some 70120310187665451902745009356331 := by
  decide +kernel

theorem chunk307_length : chunk307.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
