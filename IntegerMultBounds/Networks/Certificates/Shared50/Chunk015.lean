import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk011

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk015_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 8463807665918676923669043) chunk015 = true := by
  decide +kernel

theorem chunk015_last : lastKey (some 8463807665918676923669043) chunk015 = some 8673465110282357329718247 := by
  decide +kernel

theorem chunk015_length : chunk015.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
