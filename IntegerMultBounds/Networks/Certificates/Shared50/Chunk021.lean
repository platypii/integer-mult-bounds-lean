import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk017

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk021_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 11982222286884299868906440) chunk021 = true := by
  decide +kernel

theorem chunk021_last : lastKey (some 11982222286884299868906440) chunk021 = some 12409951691738415275518853 := by
  decide +kernel

theorem chunk021_length : chunk021.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
