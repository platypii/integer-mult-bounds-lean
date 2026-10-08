import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk295

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk299_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 16777263186035302515488100500669) chunk299 = true := by
  decide +kernel

theorem chunk299_last : lastKey (some 16777263186035302515488100500669) chunk299 = some 18402532621107578692177822703015 := by
  decide +kernel

theorem chunk299_length : chunk299.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
