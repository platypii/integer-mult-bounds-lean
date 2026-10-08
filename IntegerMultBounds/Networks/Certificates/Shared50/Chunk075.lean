import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk071

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk075_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 183370091641607240139157625169) chunk075 = true := by
  decide +kernel

theorem chunk075_last : lastKey (some 183370091641607240139157625169) chunk075 = some 184339624207834422338352667225 := by
  decide +kernel

theorem chunk075_length : chunk075.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
