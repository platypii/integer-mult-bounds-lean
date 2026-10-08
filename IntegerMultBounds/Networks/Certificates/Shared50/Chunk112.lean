import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk108

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk112_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 395022758175693791751534863058) chunk112 = true := by
  decide +kernel

theorem chunk112_last : lastKey (some 395022758175693791751534863058) chunk112 = some 409123336686214569583432076658 := by
  decide +kernel

theorem chunk112_length : chunk112.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
