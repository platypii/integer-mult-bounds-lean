import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk021

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk025_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 15359230309270474392260362) chunk025 = true := by
  decide +kernel

theorem chunk025_last : lastKey (some 15359230309270474392260362) chunk025 = some 15981703866206165008177223 := by
  decide +kernel

theorem chunk025_length : chunk025.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
