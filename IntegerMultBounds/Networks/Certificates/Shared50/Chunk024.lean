import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk020

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk024_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 14424217440792050098872907) chunk024 = true := by
  decide +kernel

theorem chunk024_last : lastKey (some 14424217440792050098872907) chunk024 = some 15359230309270474392260362 := by
  decide +kernel

theorem chunk024_length : chunk024.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
