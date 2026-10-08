import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk190

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk194_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1734128728966233556843013899419) chunk194 = true := by
  decide +kernel

theorem chunk194_last : lastKey (some 1734128728966233556843013899419) chunk194 = some 1745676639524612521450863689819 := by
  decide +kernel

theorem chunk194_length : chunk194.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
