import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk051

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk055_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 79868733603908639612308823) chunk055 = true := by
  decide +kernel

theorem chunk055_last : lastKey (some 79868733603908639612308823) chunk055 = some 82874295756701076544980643 := by
  decide +kernel

theorem chunk055_length : chunk055.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
