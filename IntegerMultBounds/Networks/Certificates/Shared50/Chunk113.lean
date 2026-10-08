import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk109

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk113_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 409123336686214569583432076658) chunk113 = true := by
  decide +kernel

theorem chunk113_last : lastKey (some 409123336686214569583432076658) chunk113 = some 411734404049348382727004518690 := by
  decide +kernel

theorem chunk113_length : chunk113.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
