import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk159

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk163_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1034056096947752203196977101497) chunk163 = true := by
  decide +kernel

theorem chunk163_last : lastKey (some 1034056096947752203196977101497) chunk163 = some 1039929830020921808349176475641 := by
  decide +kernel

theorem chunk163_length : chunk163.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
