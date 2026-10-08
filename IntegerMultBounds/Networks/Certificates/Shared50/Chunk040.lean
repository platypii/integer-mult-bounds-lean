import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk036

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk040_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 32467509422863003952672411) chunk040 = true := by
  decide +kernel

theorem chunk040_last : lastKey (some 32467509422863003952672411) chunk040 = some 35619179648600928869405328 := by
  decide +kernel

theorem chunk040_length : chunk040.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
