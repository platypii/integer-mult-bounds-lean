import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk214

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk218_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2597304471497664398289283327003) chunk218 = true := by
  decide +kernel

theorem chunk218_last : lastKey (some 2597304471497664398289283327003) chunk218 = some 2617045301691821877897852058783 := by
  decide +kernel

theorem chunk218_length : chunk218.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
