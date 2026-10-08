import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Chunk053

/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.
Regenerate with scripts/generate_shared50_witnesses.py. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50
open SharedPointWitnessCheck
set_option maxRecDepth 8192

theorem chunk057_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup
    (some 91652695836124852172212644) chunk057 = true := by
  decide +kernel

theorem chunk057_last : lastKey (some 91652695836124852172212644) chunk057 = some 96775305688738645231965621 := by
  decide +kernel

theorem chunk057_length : chunk057.length = 128 := by rfl

end IntegerMultBounds.Networks.Certificates.Shared50
