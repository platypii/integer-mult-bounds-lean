import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk163

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk167_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1078828590755187276221944782241) chunk167 = true := by
  decide +kernel

theorem chunk167_last : lastKey (some 1078828590755187276221944782241) chunk167 = some 1086453188614123410281215706192 := by
  decide +kernel

theorem chunk167_length : chunk167.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
