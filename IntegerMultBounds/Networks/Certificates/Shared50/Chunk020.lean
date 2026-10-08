import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk016

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk020_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 11567051028818213711948360) chunk020 = true := by
  decide +kernel

theorem chunk020_last : lastKey (some 11567051028818213711948360) chunk020 = some 11982222286884299868906440 := by
  decide +kernel

theorem chunk020_length : chunk020.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
