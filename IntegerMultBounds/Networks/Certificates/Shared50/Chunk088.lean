import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk084

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk088_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 236094803250718607574966307451) chunk088 = true := by
  decide +kernel

theorem chunk088_last : lastKey (some 236094803250718607574966307451) chunk088 = some 247177022083257511988601838283 := by
  decide +kernel

theorem chunk088_length : chunk088.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
