import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk106

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk110_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 388754430987624548289284537095) chunk110 = true := by
  decide +kernel

theorem chunk110_last : lastKey (some 388754430987624548289284537095) chunk110 = some 393132702024809059760913411145 := by
  decide +kernel

theorem chunk110_length : chunk110.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
