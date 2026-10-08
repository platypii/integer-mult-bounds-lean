import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk047

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk051_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 63458206685447522523935426) chunk051 = true := by
  decide +kernel

theorem chunk051_last : lastKey (some 63458206685447522523935426) chunk051 = some 65917985328550854959191225 := by
  decide +kernel

theorem chunk051_length : chunk051.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
