import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk121

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk125_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 511208411710576168818310471020) chunk125 = true := by
  decide +kernel

theorem chunk125_last : lastKey (some 511208411710576168818310471020) chunk125 = some 515176473233021995749668889611 := by
  decide +kernel

theorem chunk125_length : chunk125.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
