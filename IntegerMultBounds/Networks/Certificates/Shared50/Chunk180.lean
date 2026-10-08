import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk176

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk180_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1332767631254533090425337693939) chunk180 = true := by
  decide +kernel

theorem chunk180_last : lastKey (some 1332767631254533090425337693939) chunk180 = some 1349316706325027472938292277507 := by
  decide +kernel

theorem chunk180_length : chunk180.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
