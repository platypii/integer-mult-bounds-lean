import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk078

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk082_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 208276963220246861376225900103) chunk082 = true := by
  decide +kernel

theorem chunk082_last : lastKey (some 208276963220246861376225900103) chunk082 = some 210086009548561291056968052444 := by
  decide +kernel

theorem chunk082_length : chunk082.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
