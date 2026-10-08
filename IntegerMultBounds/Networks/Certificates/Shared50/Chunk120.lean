import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk116

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk120_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 461283129213590269095933196233) chunk120 = true := by
  decide +kernel

theorem chunk120_last : lastKey (some 461283129213590269095933196233) chunk120 = some 472975744078289608519186229912 := by
  decide +kernel

theorem chunk120_length : chunk120.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
