import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk219

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk223_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2860824303173956796595122503875) chunk223 = true := by
  decide +kernel

theorem chunk223_last : lastKey (some 2860824303173956796595122503875) chunk223 = some 2878720599731616643585159921251 := by
  decide +kernel

theorem chunk223_length : chunk223.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
