import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk006

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk010_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 6940106379044151224511612) chunk010 = true := by
  decide +kernel

theorem chunk010_last : lastKey (some 6940106379044151224511612) chunk010 = some 7296822759827866864602251 := by
  decide +kernel

theorem chunk010_length : chunk010.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
