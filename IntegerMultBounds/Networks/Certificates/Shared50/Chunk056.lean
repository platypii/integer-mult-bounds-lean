import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk052

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk056_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 82874295756701076544980643) chunk056 = true := by
  decide +kernel

theorem chunk056_last : lastKey (some 82874295756701076544980643) chunk056 = some 91652695836124852172212644 := by
  decide +kernel

theorem chunk056_length : chunk056.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
