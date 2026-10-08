import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk164

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk168_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1086453188614123410281215706192) chunk168 = true := by
  decide +kernel

theorem chunk168_last : lastKey (some 1086453188614123410281215706192) chunk168 = some 1118994454078315654662266172980 := by
  decide +kernel

theorem chunk168_length : chunk168.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
