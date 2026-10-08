import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk157

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk161_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 971330131532041238681614890017) chunk161 = true := by
  decide +kernel

theorem chunk161_last : lastKey (some 971330131532041238681614890017) chunk161 = some 979680613343432345316196316117 := by
  decide +kernel

theorem chunk161_length : chunk161.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
