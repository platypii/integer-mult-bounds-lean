import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk102

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk106_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 352374165389481295916586265935) chunk106 = true := by
  decide +kernel

theorem chunk106_last : lastKey (some 352374165389481295916586265935) chunk106 = some 365723975049334442614275067327 := by
  decide +kernel

theorem chunk106_length : chunk106.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
