import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk209

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk213_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2367344027496649015390740619560) chunk213 = true := by
  decide +kernel

theorem chunk213_last : lastKey (some 2367344027496649015390740619560) chunk213 = some 2385543322718469700109267521624 := by
  decide +kernel

theorem chunk213_length : chunk213.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
