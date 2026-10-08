import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk173

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk177_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1285945997866583813157494736739) chunk177 = true := by
  decide +kernel

theorem chunk177_last : lastKey (some 1285945997866583813157494736739) chunk177 = some 1293055093958293075049886519307 := by
  decide +kernel

theorem chunk177_length : chunk177.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
