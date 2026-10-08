import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk165

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk169_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1118994454078315654662266172980) chunk169 = true := by
  decide +kernel

theorem chunk169_last : lastKey (some 1118994454078315654662266172980) chunk169 = some 1152386373120134699378081656100 := by
  decide +kernel

theorem chunk169_length : chunk169.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
