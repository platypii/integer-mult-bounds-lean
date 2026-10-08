import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk248

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk252_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4724435512497054348709902213409) chunk252 = true := by
  decide +kernel

theorem chunk252_last : lastKey (some 4724435512497054348709902213409) chunk252 = some 4774479702692347711893799857957 := by
  decide +kernel

theorem chunk252_length : chunk252.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
