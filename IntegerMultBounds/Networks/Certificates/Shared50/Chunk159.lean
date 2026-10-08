import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk155

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk159_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 939887994324815362214547926826) chunk159 = true := by
  decide +kernel

theorem chunk159_last : lastKey (some 939887994324815362214547926826) chunk159 = some 945291689240414391545798369553 := by
  decide +kernel

theorem chunk159_length : chunk159.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
