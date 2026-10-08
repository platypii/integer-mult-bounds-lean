import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk254

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk258_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5264441218955221937839765268673) chunk258 = true := by
  decide +kernel

theorem chunk258_last : lastKey (some 5264441218955221937839765268673) chunk258 = some 5356412907754163197953140216196 := by
  decide +kernel

theorem chunk258_length : chunk258.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
