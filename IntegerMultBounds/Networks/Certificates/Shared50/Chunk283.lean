import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk279

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk283_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 9297783122615071447581430738314) chunk283 = true := by
  decide +kernel

theorem chunk283_last : lastKey (some 9297783122615071447581430738314) chunk283 = some 9810216066785258832874730593977 := by
  decide +kernel

theorem chunk283_length : chunk283.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
