import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk307

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk311_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 118644494425609946934975441454255) chunk311 = true := by
  decide +kernel

theorem chunk311_last : lastKey (some 118644494425609946934975441454255) chunk311 = some 140369957936036530488284116303907 := by
  decide +kernel

theorem chunk311_length : chunk311.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
