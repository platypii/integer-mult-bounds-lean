import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk166

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk170_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1152386373120134699378081656100) chunk170 = true := by
  decide +kernel

theorem chunk170_last : lastKey (some 1152386373120134699378081656100) chunk170 = some 1158845689961990093248237162028 := by
  decide +kernel

theorem chunk170_length : chunk170.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
