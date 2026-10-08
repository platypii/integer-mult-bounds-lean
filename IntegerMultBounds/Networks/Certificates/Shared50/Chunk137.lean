import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk133

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk137_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 635878383590811953001279171254) chunk137 = true := by
  decide +kernel

theorem chunk137_last : lastKey (some 635878383590811953001279171254) chunk137 = some 641644491315664112351299139054 := by
  decide +kernel

theorem chunk137_length : chunk137.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
