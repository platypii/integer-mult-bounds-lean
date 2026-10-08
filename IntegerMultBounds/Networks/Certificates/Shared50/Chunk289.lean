import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk285

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk289_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 11130381019026358676901103162169) chunk289 = true := by
  decide +kernel

theorem chunk289_last : lastKey (some 11130381019026358676901103162169) chunk289 = some 11644266210421291007128565135084 := by
  decide +kernel

theorem chunk289_length : chunk289.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
