import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk141

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk145_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 752454465957024876689916215539) chunk145 = true := by
  decide +kernel

theorem chunk145_last : lastKey (some 752454465957024876689916215539) chunk145 = some 756901908443096622712841930611 := by
  decide +kernel

theorem chunk145_length : chunk145.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
