import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk297

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk301_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 19350998405946406009058830493567) chunk301 = true := by
  decide +kernel

theorem chunk301_last : lastKey (some 19350998405946406009058830493567) chunk301 = some 21964669120315673048332147524509 := by
  decide +kernel

theorem chunk301_length : chunk301.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
