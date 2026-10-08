import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk221

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk225_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2900318196254945801029190742570) chunk225 = true := by
  decide +kernel

theorem chunk225_last : lastKey (some 2900318196254945801029190742570) chunk225 = some 2918430957756080657681595026427 := by
  decide +kernel

theorem chunk225_length : chunk225.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
