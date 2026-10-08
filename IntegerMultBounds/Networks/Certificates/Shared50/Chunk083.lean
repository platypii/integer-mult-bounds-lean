import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk079

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk083_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 210086009548561291056968052444) chunk083 = true := by
  decide +kernel

theorem chunk083_last : lastKey (some 210086009548561291056968052444) chunk083 = some 219717546725505867185710349287 := by
  decide +kernel

theorem chunk083_length : chunk083.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
