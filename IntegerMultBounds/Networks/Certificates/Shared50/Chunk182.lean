import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk178

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk182_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1415406597126944005534489496377) chunk182 = true := by
  decide +kernel

theorem chunk182_last : lastKey (some 1415406597126944005534489496377) chunk182 = some 1423139711887934973243890822905 := by
  decide +kernel

theorem chunk182_length : chunk182.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
