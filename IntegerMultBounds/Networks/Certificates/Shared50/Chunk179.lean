import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk175

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk179_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1301985140985520118680247215267) chunk179 = true := by
  decide +kernel

theorem chunk179_last : lastKey (some 1301985140985520118680247215267) chunk179 = some 1332767631254533090425337693939 := by
  decide +kernel

theorem chunk179_length : chunk179.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
