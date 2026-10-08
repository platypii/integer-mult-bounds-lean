import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk110

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk114_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 411734404049348382727004518690) chunk114 = true := by
  decide +kernel

theorem chunk114_last : lastKey (some 411734404049348382727004518690) chunk114 = some 416337623941539029835447927234 := by
  decide +kernel

theorem chunk114_length : chunk114.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
