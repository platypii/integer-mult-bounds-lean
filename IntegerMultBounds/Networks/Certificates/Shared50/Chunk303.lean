import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk299

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk303_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 26968249085462243900405623696919) chunk303 = true := by
  decide +kernel

theorem chunk303_last : lastKey (some 26968249085462243900405623696919) chunk303 = some 32911852416382475429098715768182 := by
  decide +kernel

theorem chunk303_length : chunk303.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
