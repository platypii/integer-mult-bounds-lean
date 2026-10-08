import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk068

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk072_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 164597918343092546021348181905) chunk072 = true := by
  decide +kernel

theorem chunk072_last : lastKey (some 164597918343092546021348181905) chunk072 = some 165775188491222894341049200897 := by
  decide +kernel

theorem chunk072_length : chunk072.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
