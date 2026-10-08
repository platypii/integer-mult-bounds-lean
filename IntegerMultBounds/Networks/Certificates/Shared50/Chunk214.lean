import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk210

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk214_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 2385543322718469700109267521624) chunk214 = true := by
  decide +kernel

theorem chunk214_last : lastKey (some 2385543322718469700109267521624) chunk214 = some 2400808539241320812252417237593 := by
  decide +kernel

theorem chunk214_length : chunk214.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
