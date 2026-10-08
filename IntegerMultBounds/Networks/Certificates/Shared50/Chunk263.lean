import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk259

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk263_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5811103396784137377319102222371) chunk263 = true := by
  decide +kernel

theorem chunk263_last : lastKey (some 5811103396784137377319102222371) chunk263 = some 6179181916653355032296793739298 := by
  decide +kernel

theorem chunk263_length : chunk263.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
