import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk001

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk005_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5171284780384988215604197) chunk005 = true := by
  decide +kernel

theorem chunk005_last : lastKey (some 5171284780384988215604197) chunk005 = some 5342388478392164877459076 := by
  decide +kernel

theorem chunk005_length : chunk005.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
