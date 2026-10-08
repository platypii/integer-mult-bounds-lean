import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk038

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk042_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 38060044248512154921801997) chunk042 = true := by
  decide +kernel

theorem chunk042_last : lastKey (some 38060044248512154921801997) chunk042 = some 39834278161898176501813022 := by
  decide +kernel

theorem chunk042_length : chunk042.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
