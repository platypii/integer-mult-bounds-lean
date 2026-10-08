import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk010

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk014_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 8207815960926610532097892) chunk014 = true := by
  decide +kernel

theorem chunk014_last : lastKey (some 8207815960926610532097892) chunk014 = some 8463807665918676923669043 := by
  decide +kernel

theorem chunk014_length : chunk014.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
