import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk027

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk031_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 20988185784837850468518925) chunk031 = true := by
  decide +kernel

theorem chunk031_last : lastKey (some 20988185784837850468518925) chunk031 = some 22043803555089849837225298 := by
  decide +kernel

theorem chunk031_length : chunk031.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
