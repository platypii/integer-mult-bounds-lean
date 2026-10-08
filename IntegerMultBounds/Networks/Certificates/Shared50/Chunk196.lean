import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk192

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk196_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1757291782172236097908409188224) chunk196 = true := by
  decide +kernel

theorem chunk196_last : lastKey (some 1757291782172236097908409188224) chunk196 = some 1768975074209175625549024551959 := by
  decide +kernel

theorem chunk196_length : chunk196.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
