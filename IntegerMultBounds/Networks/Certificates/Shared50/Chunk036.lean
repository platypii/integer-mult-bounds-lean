import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk032

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk036_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 27316399022370851749591115) chunk036 = true := by
  decide +kernel

theorem chunk036_last : lastKey (some 27316399022370851749591115) chunk036 = some 29099913865769169180807932 := by
  decide +kernel

theorem chunk036_length : chunk036.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
