import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk152

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk156_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 882206700686172123911285376114) chunk156 = true := by
  decide +kernel

theorem chunk156_last : lastKey (some 882206700686172123911285376114) chunk156 = some 926493671726488068973914377823 := by
  decide +kernel

theorem chunk156_length : chunk156.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
