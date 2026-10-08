import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk034

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk038_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 30345569194572378253348426) chunk038 = true := by
  decide +kernel

theorem chunk038_last : lastKey (some 30345569194572378253348426) chunk038 = some 31472320250937623731270287 := by
  decide +kernel

theorem chunk038_length : chunk038.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
