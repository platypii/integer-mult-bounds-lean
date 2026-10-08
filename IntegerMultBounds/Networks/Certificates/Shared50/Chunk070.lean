import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk066

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk070_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 627111670341848295890525169) chunk070 = true := by
  decide +kernel

theorem chunk070_last : lastKey (some 627111670341848295890525169) chunk070 = some 163719414781361461589207201090 := by
  decide +kernel

theorem chunk070_length : chunk070.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
