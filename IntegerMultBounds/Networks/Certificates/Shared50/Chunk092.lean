import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk088

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk092_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 262220146573464713356609434030) chunk092 = true := by
  decide +kernel

theorem chunk092_last : lastKey (some 262220146573464713356609434030) chunk092 = some 264433334236780192374842969801 := by
  decide +kernel

theorem chunk092_length : chunk092.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
