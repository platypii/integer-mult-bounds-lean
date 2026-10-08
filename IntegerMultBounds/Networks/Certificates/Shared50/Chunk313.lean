import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk309

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk313_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 165375522385355544551288770130022) chunk313 = true := by
  decide +kernel

theorem chunk313_last : lastKey (some 165375522385355544551288770130022) chunk313 = some 194911311484817956081226537279087 := by
  decide +kernel

theorem chunk313_length : chunk313.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
