import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk135

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk139_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 677213735210266283360902510576) chunk139 = true := by
  decide +kernel

theorem chunk139_last : lastKey (some 677213735210266283360902510576) chunk139 = some 680255864375196916343005182037 := by
  decide +kernel

theorem chunk139_length : chunk139.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
