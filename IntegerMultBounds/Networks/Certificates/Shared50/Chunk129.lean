import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk125

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk129_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 550426253577176829143120131139) chunk129 = true := by
  decide +kernel

theorem chunk129_last : lastKey (some 550426253577176829143120131139) chunk129 = some 567530095280444572400804803211 := by
  decide +kernel

theorem chunk129_length : chunk129.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
