import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk264

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk268_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 6472121877532960506758910912755) chunk268 = true := by
  decide +kernel

theorem chunk268_last : lastKey (some 6472121877532960506758910912755) chunk268 = some 6799948002191032646559840809573 := by
  decide +kernel

theorem chunk268_length : chunk268.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
