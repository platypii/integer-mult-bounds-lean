import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk267

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk271_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 6969238476314250831146984323126) chunk271 = true := by
  decide +kernel

theorem chunk271_last : lastKey (some 6969238476314250831146984323126) chunk271 = some 7094667338319638720890560060262 := by
  decide +kernel

theorem chunk271_length : chunk271.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
