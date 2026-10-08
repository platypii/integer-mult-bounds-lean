import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk177

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk181_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1349316706325027472938292277507) chunk181 = true := by
  decide +kernel

theorem chunk181_last : lastKey (some 1349316706325027472938292277507) chunk181 = some 1415406597126944005534489496377 := by
  decide +kernel

theorem chunk181_length : chunk181.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
