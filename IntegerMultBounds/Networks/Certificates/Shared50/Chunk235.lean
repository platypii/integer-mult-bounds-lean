import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk231

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk235_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3501260478466436854764711019612) chunk235 = true := by
  decide +kernel

theorem chunk235_last : lastKey (some 3501260478466436854764711019612) chunk235 = some 3526895602249048271815552327744 := by
  decide +kernel

theorem chunk235_length : chunk235.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
