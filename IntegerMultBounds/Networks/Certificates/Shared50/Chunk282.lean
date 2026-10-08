import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk278

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk282_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 9168453446155737218796227125542) chunk282 = true := by
  decide +kernel

theorem chunk282_last : lastKey (some 9168453446155737218796227125542) chunk282 = some 9297783122615071447581430738314 := by
  decide +kernel

theorem chunk282_length : chunk282.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
