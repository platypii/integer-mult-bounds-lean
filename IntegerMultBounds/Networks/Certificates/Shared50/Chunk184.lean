import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk180

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk184_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1432852768880211980563945623822) chunk184 = true := by
  decide +kernel

theorem chunk184_last : lastKey (some 1432852768880211980563945623822) chunk184 = some 1440669688595425442772122240982 := by
  decide +kernel

theorem chunk184_length : chunk184.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
