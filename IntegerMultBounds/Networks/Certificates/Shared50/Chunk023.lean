import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk019

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk023_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 12703013060125374523690005) chunk023 = true := by
  decide +kernel

theorem chunk023_last : lastKey (some 12703013060125374523690005) chunk023 = some 14424217440792050098872907 := by
  decide +kernel

theorem chunk023_length : chunk023.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
