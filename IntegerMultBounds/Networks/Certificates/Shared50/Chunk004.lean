import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk000

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk004_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4972654219697812664490385) chunk004 = true := by
  decide +kernel

theorem chunk004_last : lastKey (some 4972654219697812664490385) chunk004 = some 5171284780384988215604197 := by
  decide +kernel

theorem chunk004_length : chunk004.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
