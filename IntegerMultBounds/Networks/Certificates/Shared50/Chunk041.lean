import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk037

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk041_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 35619179648600928869405328) chunk041 = true := by
  decide +kernel

theorem chunk041_last : lastKey (some 35619179648600928869405328) chunk041 = some 38060044248512154921801997 := by
  decide +kernel

theorem chunk041_length : chunk041.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
