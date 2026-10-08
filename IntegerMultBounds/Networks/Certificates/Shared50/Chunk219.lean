import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk215

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk219_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2617045301691821877897852058783) chunk219 = true := by
  decide +kernel

theorem chunk219_last : lastKey (some 2617045301691821877897852058783) chunk219 = some 2636917556382442973360195060011 := by
  decide +kernel

theorem chunk219_length : chunk219.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
