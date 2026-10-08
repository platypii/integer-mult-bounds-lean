import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk041

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk045_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 42737867581357151581014301) chunk045 = true := by
  decide +kernel

theorem chunk045_last : lastKey (some 42737867581357151581014301) chunk045 = some 47673605944184322452944050 := by
  decide +kernel

theorem chunk045_length : chunk045.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
