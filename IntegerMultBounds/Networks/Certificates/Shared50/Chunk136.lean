import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk132

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk136_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 616052721177086371880216146142) chunk136 = true := by
  decide +kernel

theorem chunk136_last : lastKey (some 616052721177086371880216146142) chunk136 = some 635878383590811953001279171254 := by
  decide +kernel

theorem chunk136_length : chunk136.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
