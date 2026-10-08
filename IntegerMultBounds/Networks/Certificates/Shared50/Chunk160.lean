import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk156

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk160_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 945291689240414391545798369553) chunk160 = true := by
  decide +kernel

theorem chunk160_last : lastKey (some 945291689240414391545798369553) chunk160 = some 971330131532041238681614890017 := by
  decide +kernel

theorem chunk160_length : chunk160.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
