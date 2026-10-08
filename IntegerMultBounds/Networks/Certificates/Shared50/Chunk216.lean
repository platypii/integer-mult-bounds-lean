import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk212

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk216_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2447116258992066724980078242088) chunk216 = true := by
  decide +kernel

theorem chunk216_last : lastKey (some 2447116258992066724980078242088) chunk216 = some 2500534593337327818117759198808 := by
  decide +kernel

theorem chunk216_length : chunk216.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
