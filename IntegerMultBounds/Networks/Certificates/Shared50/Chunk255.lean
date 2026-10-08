import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk251

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk255_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5126099326790228406670125504057) chunk255 = true := by
  decide +kernel

theorem chunk255_last : lastKey (some 5126099326790228406670125504057) chunk255 = some 5173849530526568340664727376521 := by
  decide +kernel

theorem chunk255_length : chunk255.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
