import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk270

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk274_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 7566058371229937825209542003400) chunk274 = true := by
  decide +kernel

theorem chunk274_last : lastKey (some 7566058371229937825209542003400) chunk274 = some 7650044279261847497191954367205 := by
  decide +kernel

theorem chunk274_length : chunk274.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
