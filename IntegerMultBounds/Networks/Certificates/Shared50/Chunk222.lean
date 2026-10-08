import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk218

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk222_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2707520992574138075754849960027) chunk222 = true := by
  decide +kernel

theorem chunk222_last : lastKey (some 2707520992574138075754849960027) chunk222 = some 2860824303173956796595122503875 := by
  decide +kernel

theorem chunk222_length : chunk222.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
