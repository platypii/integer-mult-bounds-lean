import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk240

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk244_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4012457597187324661708491457631) chunk244 = true := by
  decide +kernel

theorem chunk244_last : lastKey (some 4012457597187324661708491457631) chunk244 = some 4233525118464124431077401763599 := by
  decide +kernel

theorem chunk244_length : chunk244.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
