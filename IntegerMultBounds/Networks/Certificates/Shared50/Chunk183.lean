import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk179

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk183_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1423139711887934973243890822905) chunk183 = true := by
  decide +kernel

theorem chunk183_last : lastKey (some 1423139711887934973243890822905) chunk183 = some 1432852768880211980563945623822 := by
  decide +kernel

theorem chunk183_length : chunk183.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
