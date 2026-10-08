import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk232

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk236_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 3526895602249048271815552327744) chunk236 = true := by
  decide +kernel

theorem chunk236_last : lastKey (some 3526895602249048271815552327744) chunk236 = some 3552695460192695781020241978109 := by
  decide +kernel

theorem chunk236_length : chunk236.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
