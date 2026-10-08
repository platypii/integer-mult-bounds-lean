import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk026

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk030_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 19541395995667956844036524) chunk030 = true := by
  decide +kernel

theorem chunk030_last : lastKey (some 19541395995667956844036524) chunk030 = some 20988185784837850468518925 := by
  decide +kernel

theorem chunk030_length : chunk030.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
