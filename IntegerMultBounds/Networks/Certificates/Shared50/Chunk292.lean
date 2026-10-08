import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk288

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk292_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 12318935537935748735714244409679) chunk292 = true := by
  decide +kernel

theorem chunk292_last : lastKey (some 12318935537935748735714244409679) chunk292 = some 13027566897095870945880619836531 := by
  decide +kernel

theorem chunk292_length : chunk292.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
