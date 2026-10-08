import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk153

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk157_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 926493671726488068973914377823) chunk157 = true := by
  decide +kernel

theorem chunk157_last : lastKey (some 926493671726488068973914377823) chunk157 = some 934511467424971496765501473698 := by
  decide +kernel

theorem chunk157_length : chunk157.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
