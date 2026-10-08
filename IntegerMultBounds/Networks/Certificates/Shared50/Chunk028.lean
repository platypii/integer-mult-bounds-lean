import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk024

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk028_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 17291831463153788775071055) chunk028 = true := by
  decide +kernel

theorem chunk028_last : lastKey (some 17291831463153788775071055) chunk028 = some 17683830170413138763733368 := by
  decide +kernel

theorem chunk028_length : chunk028.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
