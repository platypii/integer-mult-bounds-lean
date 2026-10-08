import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk283

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk287_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 10783716472535285165829230257256) chunk287 = true := by
  decide +kernel

theorem chunk287_last : lastKey (some 10783716472535285165829230257256) chunk287 = some 10944302151177800755696624166041 := by
  decide +kernel

theorem chunk287_length : chunk287.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
