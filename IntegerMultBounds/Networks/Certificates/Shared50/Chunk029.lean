import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk025

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk029_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 17683830170413138763733368) chunk029 = true := by
  decide +kernel

theorem chunk029_last : lastKey (some 17683830170413138763733368) chunk029 = some 19541395995667956844036524 := by
  decide +kernel

theorem chunk029_length : chunk029.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
