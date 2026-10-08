import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk035

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk039_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 31472320250937623731270287) chunk039 = true := by
  decide +kernel

theorem chunk039_last : lastKey (some 31472320250937623731270287) chunk039 = some 32467509422863003952672411 := by
  decide +kernel

theorem chunk039_length : chunk039.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
