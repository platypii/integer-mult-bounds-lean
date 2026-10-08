import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk067

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk071_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 163719414781361461589207201090) chunk071 = true := by
  decide +kernel

theorem chunk071_last : lastKey (some 163719414781361461589207201090) chunk071 = some 164597918343092546021348181905 := by
  decide +kernel

theorem chunk071_length : chunk071.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
