import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk042

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk046_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 47673605944184322452944050) chunk046 = true := by
  decide +kernel

theorem chunk046_last : lastKey (some 47673605944184322452944050) chunk046 = some 50570884830631279469173239 := by
  decide +kernel

theorem chunk046_length : chunk046.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
