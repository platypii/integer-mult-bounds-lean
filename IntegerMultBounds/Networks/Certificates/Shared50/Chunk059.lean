import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk055

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk059_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 99879677821137648042323542) chunk059 = true := by
  decide +kernel

theorem chunk059_last : lastKey (some 99879677821137648042323542) chunk059 = some 111680969002208610419601687 := by
  decide +kernel

theorem chunk059_length : chunk059.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
