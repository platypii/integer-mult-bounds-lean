import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk275

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk279_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 8415824101415684145535275984055) chunk279 = true := by
  decide +kernel

theorem chunk279_last : lastKey (some 8415824101415684145535275984055) chunk279 = some 8895221758284031611723061260139 := by
  decide +kernel

theorem chunk279_length : chunk279.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
