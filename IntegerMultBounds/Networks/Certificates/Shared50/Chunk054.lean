import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk050

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk054_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 76247022090243782264820043) chunk054 = true := by
  decide +kernel

theorem chunk054_last : lastKey (some 76247022090243782264820043) chunk054 = some 79868733603908639612308823 := by
  decide +kernel

theorem chunk054_length : chunk054.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
