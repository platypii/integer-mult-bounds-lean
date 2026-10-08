import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk070

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk074_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 167554775753837709173513522501) chunk074 = true := by
  decide +kernel

theorem chunk074_last : lastKey (some 167554775753837709173513522501) chunk074 = some 183370091641607240139157625169 := by
  decide +kernel

theorem chunk074_length : chunk074.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
