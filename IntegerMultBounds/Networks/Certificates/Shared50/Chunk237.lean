import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk233

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk237_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3552695460192695781020241978109) chunk237 = true := by
  decide +kernel

theorem chunk237_last : lastKey (some 3552695460192695781020241978109) chunk237 = some 3582998062152652132491401959949 := by
  decide +kernel

theorem chunk237_length : chunk237.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
