import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk296

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk300_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 18402532621107578692177822703015) chunk300 = true := by
  decide +kernel

theorem chunk300_last : lastKey (some 18402532621107578692177822703015) chunk300 = some 19350998405946406009058830493567 := by
  decide +kernel

theorem chunk300_length : chunk300.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
