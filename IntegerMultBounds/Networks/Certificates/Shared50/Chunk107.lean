import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk103

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk107_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 365723975049334442614275067327) chunk107 = true := by
  decide +kernel

theorem chunk107_last : lastKey (some 365723975049334442614275067327) chunk107 = some 367499268007223610827580595606 := by
  decide +kernel

theorem chunk107_length : chunk107.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
