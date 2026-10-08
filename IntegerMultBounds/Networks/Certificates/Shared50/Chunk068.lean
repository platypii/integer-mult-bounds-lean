import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk064

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk068_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 210792828529961700077420434) chunk068 = true := by
  decide +kernel

theorem chunk068_last : lastKey (some 210792828529961700077420434) chunk068 = some 239111148983061146145580872 := by
  decide +kernel

theorem chunk068_length : chunk068.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
