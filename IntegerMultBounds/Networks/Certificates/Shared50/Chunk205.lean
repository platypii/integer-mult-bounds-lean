import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk201

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk205_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2019985534340312099048476768103) chunk205 = true := by
  decide +kernel

theorem chunk205_last : lastKey (some 2019985534340312099048476768103) chunk205 = some 2122193630830785950216055039901 := by
  decide +kernel

theorem chunk205_length : chunk205.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
