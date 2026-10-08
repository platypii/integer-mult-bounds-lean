import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk161

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk165_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 1045832737053009707318549460305) chunk165 = true := by
  decide +kernel

theorem chunk165_last : lastKey (some 1045832737053009707318549460305) chunk165 = some 1051765204903510600477685061977 := by
  decide +kernel

theorem chunk165_length : chunk165.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
