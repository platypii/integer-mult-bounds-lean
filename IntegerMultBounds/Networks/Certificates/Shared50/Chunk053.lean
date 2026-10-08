import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk049

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk053_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 68136147421630164534729141) chunk053 = true := by
  decide +kernel

theorem chunk053_last : lastKey (some 68136147421630164534729141) chunk053 = some 76247022090243782264820043 := by
  decide +kernel

theorem chunk053_length : chunk053.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
