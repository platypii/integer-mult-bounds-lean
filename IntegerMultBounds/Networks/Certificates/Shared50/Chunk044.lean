import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk040

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk044_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 41471278854596569155274288) chunk044 = true := by
  decide +kernel

theorem chunk044_last : lastKey (some 41471278854596569155274288) chunk044 = some 42737867581357151581014301 := by
  decide +kernel

theorem chunk044_length : chunk044.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
