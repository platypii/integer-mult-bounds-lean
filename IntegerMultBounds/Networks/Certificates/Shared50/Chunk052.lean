import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk048

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk052_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 65917985328550854959191225) chunk052 = true := by
  decide +kernel

theorem chunk052_last : lastKey (some 65917985328550854959191225) chunk052 = some 68136147421630164534729141 := by
  decide +kernel

theorem chunk052_length : chunk052.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
