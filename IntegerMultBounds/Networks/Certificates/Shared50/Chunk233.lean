import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk229

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk233_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3293898145136942699197682888190) chunk233 = true := by
  decide +kernel

theorem chunk233_last : lastKey (some 3293898145136942699197682888190) chunk233 = some 3475788538938547764572714416412 := by
  decide +kernel

theorem chunk233_length : chunk233.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
