import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk113

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk117_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 440039446988401962517228812033) chunk117 = true := by
  decide +kernel

theorem chunk117_last : lastKey (some 440039446988401962517228812033) chunk117 = some 455531211330716179313676438569 := by
  decide +kernel

theorem chunk117_length : chunk117.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
