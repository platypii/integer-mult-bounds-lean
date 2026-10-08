import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk131

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk135_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 613262970066536553682322298769) chunk135 = true := by
  decide +kernel

theorem chunk135_last : lastKey (some 613262970066536553682322298769) chunk135 = some 616052721177086371880216146142 := by
  decide +kernel

theorem chunk135_length : chunk135.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
