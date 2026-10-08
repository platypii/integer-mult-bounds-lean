import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk255

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk259_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5356412907754163197953140216196) chunk259 = true := by
  decide +kernel

theorem chunk259_last : lastKey (some 5356412907754163197953140216196) chunk259 = some 5627910620632067761604511588804 := by
  decide +kernel

theorem chunk259_length : chunk259.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
