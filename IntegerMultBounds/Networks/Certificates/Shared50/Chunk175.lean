import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk171

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk175_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1249182058272538932865194359543) chunk175 = true := by
  decide +kernel

theorem chunk175_last : lastKey (some 1249182058272538932865194359543) chunk175 = some 1278871275885861859125106673707 := by
  decide +kernel

theorem chunk175_length : chunk175.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
