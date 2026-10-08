import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk015

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk019_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 11164131353099754086403893) chunk019 = true := by
  decide +kernel

theorem chunk019_last : lastKey (some 11164131353099754086403893) chunk019 = some 11567051028818213711948360 := by
  decide +kernel

theorem chunk019_length : chunk019.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
