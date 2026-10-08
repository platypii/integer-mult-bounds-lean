import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk075

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk079_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 189255391033198496670234654724) chunk079 = true := by
  decide +kernel

theorem chunk079_last : lastKey (some 189255391033198496670234654724) chunk079 = some 202226191977313291932239274919 := by
  decide +kernel

theorem chunk079_length : chunk079.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
