import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk005

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk009_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 6434004854026918735678279) chunk009 = true := by
  decide +kernel

theorem chunk009_last : lastKey (some 6434004854026918735678279) chunk009 = some 6940106379044151224511612 := by
  decide +kernel

theorem chunk009_length : chunk009.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
