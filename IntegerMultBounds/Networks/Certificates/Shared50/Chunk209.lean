import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk205

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk209_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2166563936898567987632043696125) chunk209 = true := by
  decide +kernel

theorem chunk209_last : lastKey (some 2166563936898567987632043696125) chunk209 = some 2197533274522631365374058393661 := by
  decide +kernel

theorem chunk209_length : chunk209.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
