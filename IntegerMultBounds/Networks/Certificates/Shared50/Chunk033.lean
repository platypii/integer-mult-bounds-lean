import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk029

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk033_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 23020562421832770006802712) chunk033 = true := by
  decide +kernel

theorem chunk033_last : lastKey (some 23020562421832770006802712) chunk033 = some 23778104052499033745052809 := by
  decide +kernel

theorem chunk033_length : chunk033.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
