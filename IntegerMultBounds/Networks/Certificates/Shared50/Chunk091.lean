import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk087

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk091_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 260461762727604138067925427774) chunk091 = true := by
  decide +kernel

theorem chunk091_last : lastKey (some 260461762727604138067925427774) chunk091 = some 262220146573464713356609434030 := by
  decide +kernel

theorem chunk091_length : chunk091.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
