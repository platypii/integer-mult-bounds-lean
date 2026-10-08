import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk202

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk206_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2122193630830785950216055039901) chunk206 = true := by
  decide +kernel

theorem chunk206_last : lastKey (some 2122193630830785950216055039901) chunk206 = some 2135974716802502707434242159261 := by
  decide +kernel

theorem chunk206_length : chunk206.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
