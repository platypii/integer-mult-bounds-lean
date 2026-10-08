import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk004

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk008_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 5662537049021407686050481) chunk008 = true := by
  decide +kernel

theorem chunk008_last : lastKey (some 5662537049021407686050481) chunk008 = some 6434004854026918735678279 := by
  decide +kernel

theorem chunk008_length : chunk008.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
