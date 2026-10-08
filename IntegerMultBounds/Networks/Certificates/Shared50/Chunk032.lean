import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk028

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk032_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 22043803555089849837225298) chunk032 = true := by
  decide +kernel

theorem chunk032_last : lastKey (some 22043803555089849837225298) chunk032 = some 23020562421832770006802712 := by
  decide +kernel

theorem chunk032_length : chunk032.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
