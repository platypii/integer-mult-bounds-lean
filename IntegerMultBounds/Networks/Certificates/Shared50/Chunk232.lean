import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk228

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk232_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3229858138841449149985355489565) chunk232 = true := by
  decide +kernel

theorem chunk232_last : lastKey (some 3229858138841449149985355489565) chunk232 = some 3293898145136942699197682888190 := by
  decide +kernel

theorem chunk232_length : chunk232.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
