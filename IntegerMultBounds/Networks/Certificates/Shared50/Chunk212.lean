import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk208

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk212_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2352265951131177679819997262424) chunk212 = true := by
  decide +kernel

theorem chunk212_last : lastKey (some 2352265951131177679819997262424) chunk212 = some 2367344027496649015390740619560 := by
  decide +kernel

theorem chunk212_length : chunk212.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
