import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk242

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk246_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 4263796711907369468738152249630) chunk246 = true := by
  decide +kernel

theorem chunk246_last : lastKey (some 4263796711907369468738152249630) chunk246 = some 4299344738219439546044693944471 := by
  decide +kernel

theorem chunk246_length : chunk246.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
