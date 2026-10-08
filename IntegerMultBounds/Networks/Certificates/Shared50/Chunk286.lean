import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk282

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk286_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 10161806254870523464700250733002) chunk286 = true := by
  decide +kernel

theorem chunk286_last : lastKey (some 10161806254870523464700250733002) chunk286 = some 10783716472535285165829230257256 := by
  decide +kernel

theorem chunk286_length : chunk286.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
