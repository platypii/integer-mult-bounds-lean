import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk058

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk062_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 128000964957932742204002954) chunk062 = true := by
  decide +kernel

theorem chunk062_last : lastKey (some 128000964957932742204002954) chunk062 = some 134857146079349038475191321 := by
  decide +kernel

theorem chunk062_length : chunk062.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
