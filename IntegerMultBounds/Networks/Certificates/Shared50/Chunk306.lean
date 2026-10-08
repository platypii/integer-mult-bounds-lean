import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk302

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk306_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 48491877167161642536942604188763) chunk306 = true := by
  decide +kernel

theorem chunk306_last : lastKey (some 48491877167161642536942604188763) chunk306 = some 58360896419584462185563043431216 := by
  decide +kernel

theorem chunk306_length : chunk306.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
