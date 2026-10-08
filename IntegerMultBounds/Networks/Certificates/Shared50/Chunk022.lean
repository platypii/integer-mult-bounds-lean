import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk018

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk022_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 12409951691738415275518853) chunk022 = true := by
  decide +kernel

theorem chunk022_last : lastKey (some 12409951691738415275518853) chunk022 = some 12703013060125374523690005 := by
  decide +kernel

theorem chunk022_length : chunk022.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
