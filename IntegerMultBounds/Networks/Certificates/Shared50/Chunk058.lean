import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk054

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk058_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 96775305688738645231965621) chunk058 = true := by
  decide +kernel

theorem chunk058_last : lastKey (some 96775305688738645231965621) chunk058 = some 99879677821137648042323542 := by
  decide +kernel

theorem chunk058_length : chunk058.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
