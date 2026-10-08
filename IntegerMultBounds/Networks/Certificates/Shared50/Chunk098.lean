import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk094

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk098_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 295705367443311306435871580693) chunk098 = true := by
  decide +kernel

theorem chunk098_last : lastKey (some 295705367443311306435871580693) chunk098 = some 303634153964284865783848605029 := by
  decide +kernel

theorem chunk098_length : chunk098.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
