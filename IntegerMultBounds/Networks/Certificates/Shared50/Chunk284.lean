import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk280

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk284_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 9810216066785258832874730593977) chunk284 = true := by
  decide +kernel

theorem chunk284_last : lastKey (some 9810216066785258832874730593977) chunk284 = some 9979330724809788381549603811641 := by
  decide +kernel

theorem chunk284_length : chunk284.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
