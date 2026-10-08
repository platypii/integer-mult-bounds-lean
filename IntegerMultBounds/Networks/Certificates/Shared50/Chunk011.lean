import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk007

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk011_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 7296822759827866864602251) chunk011 = true := by
  decide +kernel

theorem chunk011_last : lastKey (some 7296822759827866864602251) chunk011 = some 7621584964773819453030403 := by
  decide +kernel

theorem chunk011_length : chunk011.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
