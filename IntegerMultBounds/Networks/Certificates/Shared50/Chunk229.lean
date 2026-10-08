import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk225

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk229_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3155220068208421236397127196333) chunk229 = true := by
  decide +kernel

theorem chunk229_last : lastKey (some 3155220068208421236397127196333) chunk229 = some 3178626857527823087954237991585 := by
  decide +kernel

theorem chunk229_length : chunk229.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
