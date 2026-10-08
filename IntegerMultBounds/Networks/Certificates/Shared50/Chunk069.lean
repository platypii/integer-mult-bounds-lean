import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk065

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk069_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 239111148983061146145580872) chunk069 = true := by
  decide +kernel

theorem chunk069_last : lastKey (some 239111148983061146145580872) chunk069 = some 627111670341848295890525169 := by
  decide +kernel

theorem chunk069_length : chunk069.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
