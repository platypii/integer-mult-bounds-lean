import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk188

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk192_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1635349159419443721278474574861) chunk192 = true := by
  decide +kernel

theorem chunk192_last : lastKey (some 1635349159419443721278474574861) chunk192 = some 1650726714954398943880322390045 := by
  decide +kernel

theorem chunk192_length : chunk192.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
