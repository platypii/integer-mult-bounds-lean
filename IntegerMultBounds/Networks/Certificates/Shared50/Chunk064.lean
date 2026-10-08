import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk060

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk064_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 149536345272997718319293051) chunk064 = true := by
  decide +kernel

theorem chunk064_last : lastKey (some 149536345272997718319293051) chunk064 = some 156057419155307656731016363 := by
  decide +kernel

theorem chunk064_length : chunk064.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
