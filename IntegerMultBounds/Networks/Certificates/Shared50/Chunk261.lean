import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk257

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk261_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5686235501424018197026774165091) chunk261 = true := by
  decide +kernel

theorem chunk261_last : lastKey (some 5686235501424018197026774165091) chunk261 = some 5751654863439702544370409184935 := by
  decide +kernel

theorem chunk261_length : chunk261.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
