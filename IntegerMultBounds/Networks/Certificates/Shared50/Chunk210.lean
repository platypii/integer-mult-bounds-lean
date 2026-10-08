import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk206

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk210_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2197533274522631365374058393661) chunk210 = true := by
  decide +kernel

theorem chunk210_last : lastKey (some 2197533274522631365374058393661) chunk210 = some 2249052400771347876620037757529 := by
  decide +kernel

theorem chunk210_length : chunk210.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
