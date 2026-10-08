import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk162

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk166_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1051765204903510600477685061977) chunk166 = true := by
  decide +kernel

theorem chunk166_last : lastKey (some 1051765204903510600477685061977) chunk166 = some 1078828590755187276221944782241 := by
  decide +kernel

theorem chunk166_length : chunk166.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
