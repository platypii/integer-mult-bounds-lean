import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk126

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk130_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 567530095280444572400804803211) chunk130 = true := by
  decide +kernel

theorem chunk130_last : lastKey (some 567530095280444572400804803211) chunk130 = some 571005531239357681357321237051 := by
  decide +kernel

theorem chunk130_length : chunk130.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
