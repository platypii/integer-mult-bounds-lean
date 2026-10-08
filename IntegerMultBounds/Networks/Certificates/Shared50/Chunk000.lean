import IntegerMultBounds.Networks.Certificates.Shared50.Data

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk000_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    none chunk000 = true := by
  decide +kernel

theorem chunk000_last : lastKey none chunk000 = some 4242913991422880964759557 := by
  decide +kernel

theorem chunk000_length : chunk000.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
