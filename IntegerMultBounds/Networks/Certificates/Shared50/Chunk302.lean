import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk298

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk302_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 21964669120315673048332147524509) chunk302 = true := by
  decide +kernel

theorem chunk302_last : lastKey (some 21964669120315673048332147524509) chunk302 = some 26968249085462243900405623696919 := by
  decide +kernel

theorem chunk302_length : chunk302.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
