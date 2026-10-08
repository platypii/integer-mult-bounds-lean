import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk170

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk174_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1203272925317996353178732664695) chunk174 = true := by
  decide +kernel

theorem chunk174_last : lastKey (some 1203272925317996353178732664695) chunk174 = some 1249182058272538932865194359543 := by
  decide +kernel

theorem chunk174_length : chunk174.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
