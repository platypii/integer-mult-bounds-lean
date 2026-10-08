import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk189

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk193_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1650726714954398943880322390045) chunk193 = true := by
  decide +kernel

theorem chunk193_last : lastKey (some 1650726714954398943880322390045) chunk193 = some 1734128728966233556843013899419 := by
  decide +kernel

theorem chunk193_length : chunk193.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
