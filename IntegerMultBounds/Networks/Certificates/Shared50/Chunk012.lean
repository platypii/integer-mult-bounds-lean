import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk008

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk012_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 7621584964773819453030403) chunk012 = true := by
  decide +kernel

theorem chunk012_last : lastKey (some 7621584964773819453030403) chunk012 = some 7910099978179452955186612 := by
  decide +kernel

theorem chunk012_length : chunk012.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
