import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk031

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk035_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 24556660973713019208942489) chunk035 = true := by
  decide +kernel

theorem chunk035_last : lastKey (some 24556660973713019208942489) chunk035 = some 27316399022370851749591115 := by
  decide +kernel

theorem chunk035_length : chunk035.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
